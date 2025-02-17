"""
A script to validate query edits (e.g., instantiations and erasures of quantifiers).
"""

from __future__ import annotations
from typing import Generator

from dataclasses import dataclass
from contextlib import contextmanager

import os
import csv
import sys
import json
import time
import argparse
import tempfile
import traceback
import subprocess
import multiprocessing

sys.setrecursionlimit(10**6)

@contextmanager
def status(msg: str):
    """
    A utility context manager to print a status message
    throughout the execution of a task.
    """
    color = supports_color(sys.stderr)
    try:
        if color:
            print(f"\033[2K\r{msg}...", file=sys.stderr, end="", flush=True)
        # start = time.time()
        yield
    finally:
        if color:
            print(f"\033[2K\r", file=sys.stderr, end="", flush=True)
        # print(f"{msg}: {time.time() - start:.2f}", file=sys.stderr)

def supports_color(file: sys.TextIO):
    """
    Returns True if the running system's terminal supports color, and False otherwise.
    """
    plat = sys.platform
    supported_platform = plat != "Pocket PC" and (plat != "win32" or "ANSICON" in os.environ)
    is_a_tty = hasattr(file, "isatty") and file.isatty()
    return supported_platform and is_a_tty

def eprint(*args, **kwargs) -> None:
    print(*args, **kwargs, file=sys.stderr, flush=True)

class Exp: ...

@dataclass(frozen=True)
class Application(Exp):
    args: tuple[Exp]

    def __str__(self):
        return f"({' '.join(map(str, self.args))})"

    def is_app(self, name: str) -> bool:
        return len(self.args) != 0 and self.args[0] == Atom(name)

@dataclass(frozen=True)
class Atom(Exp):
    name: str

    def __str__(self):
        return self.name

    def is_app(self, _: str) -> bool:
        return False

    def normalize(self) -> Atom:
        return self

def tokenize_smtlib2(s: str) -> Generator[tuple[int, str], None, None]:
    """
    A simple tokenizer for SMT-LIB 2
    This is a generator of tokens (position, token)
    """

    i = 0

    in_string = False
    string_start = 0
    string_buffer: str = ""

    while i < len(s):
        c = s[i]

        if in_string:
            # In a string literal
            if c == '"':
                in_string = False
                yield string_start, string_buffer + c
                string_buffer = ""
                i += 1
            elif c == "\\":
                assert i + 1 < len(s), "unexpected end of string"
                string_buffer += c + s[i + 1]
                i += 2
            else:
                string_buffer += c
                i += 1
        else:
            if c == ";":
                # Skip comments
                i += len(s[i:].partition("\n")[0])
            elif c == "(" or c == ")":
                yield i, c
                i += 1
            elif c in " \t\n\r":
                # Skip all whitespaces
                while i < len(s) and s[i] in " \t\n\r":
                    i += 1
            elif c == '"':
                in_string = True
                string_start = i
                string_buffer = c
                i += 1
            else:
                # Take characters until space or ( or )
                old_i = i
                while i < len(s) and s[i] != "(" and s[i] != ")" and not s[i] in " \t\n\r":
                    i += 1
                yield old_i, s[old_i:i]

NORMALIZE_FLAGS = {":qid", ":skolemid", ":named", ":weight", ":cid"}

def parse_smtlib2(file_path: str, normalize: bool = True) -> list[Exp]:
    """
    Parse an SMT-LIB 2 query with some normalization (e.g. removing :qid flags)
    """

    # Stack record a nested list of unclosed applications
    stack = []
    top_level = []

    with open(file_path) as f:
        # TODO: assuming string literals do not include newlines
        for line_num, line in enumerate(f):
            for pos, token in tokenize_smtlib2(line):
                if token == "(":
                    stack.append([])
                elif token == ")":
                    assert len(stack) != 0, f"{file_path}:{line_num}:{pos}: unexpected ')'"

                    args = stack.pop()

                    # Normalize some flags
                    if normalize and len(args) != 0 and args[0] == Atom("!"):
                        new_args = []
                        i = 0
                        while i < len(args):
                            arg = args[i]
                            if isinstance(arg, Atom) and arg.name in NORMALIZE_FLAGS:
                                i += 2
                            else:
                                new_args.append(arg)
                                i += 1
                        args = new_args

                        # If there are no more flags left, remove the ! call
                        if len(args) == 2:
                            exp = args[1]
                        else:
                            exp = Application(tuple(args))
                    else:
                        exp = Application(tuple(args))

                    if len(stack) == 0:
                        top_level.append(exp)
                    else:
                        stack[-1].append(exp)
                else:
                    assert len(stack) != 0, f"{file_path}:{line_num}:{pos}: atoms can not be at the top level"
                    stack[-1].append(Atom(token))

    return top_level

def get_query_file(args: argparse.Namespace):
    if hasattr(args, "log_smt") and args.log_smt is not None:
        return open(args.log_smt, "w")
    else:
        return tempfile.NamedTemporaryFile(mode="w", suffix=".smt2")

def preprocess_query(path: str) -> tuple[list[Exp], Exp]:
    """
    Parse an SMT-LIB 2 file and return all commands and the goal assertion
    Also run some sanity checks (e.g. at most one push/pop, only one check-sat and it's after all assertions)
    """
    commands = parse_smtlib2(path)
    goal = None
    found_assert = True
    found_pop = False
    found_check_sat = False

    for i in range(len(commands) - 1, -1, -1):
        if commands[i].is_app("assert"):
            assert found_check_sat, f"assertion after check-sat in {path}"
            if goal is None:
                goal = commands.pop(i)
            found_assert = True
        elif commands[i].is_app("pop"):
            assert not found_pop, f"multiple pop commands in {path}"
            assert not found_assert, f"assertion after pop in {path}"
            found_pop = True
        elif commands[i].is_app("check-sat"):
            assert not found_check_sat, f"multiple check-sat commands in {path}"
            found_check_sat = True

    assert goal is not None, f"no goal assertion found in {path}"

    return commands, goal

def run_z3(args: argparse.Namespace, path: str) -> str:
    """
    Run Z3 and return the stdout
    """
    try:
        result = subprocess.run(
            [args.z3, path],
            stdout=subprocess.PIPE,
            stderr=sys.stderr,
            timeout=args.timeout,
            text=True,
        )
        return result.stdout.strip()

    except subprocess.TimeoutExpired:
        return "timeout"

def validate_edits(
    args: argparse.Namespace,
    original_path: str,
    edited_path: str,
) -> tuple[bool, list[str]]:
    comments = [] # e.g. warnings

    with status(f"parsing original {original_path}"):
        original, original_goal = preprocess_query(original_path)

    with status(f"parsing edited {edited_path}"):
        edited, edited_goal = preprocess_query(edited_path)

    original_set = set(original)

    with get_query_file(args) as new_query:
        write_query = lambda *args: print(*args, file=new_query)

        with status("generating new query"):
            # Override set-option's
            write_query("(set-option :auto_config false)")
            write_query("(set-option :smt.mbqi false)")
            write_query(f"(set-option :random-seed {args.seed})")

            # First push all commands in the original query, but skip some commands (e.g. push, pop, set-option)
            for cmd in original:
                if (
                    cmd.is_app("push") or
                    cmd.is_app("pop") or
                    cmd.is_app("set-option") or
                    cmd.is_app("set-info") or
                    cmd.is_app("check-sat")
                ): continue
                write_query(cmd)

            for cmd in edited:
                if (
                    cmd.is_app("push") or
                    cmd.is_app("pop") or
                    cmd.is_app("set-option") or
                    cmd.is_app("set-info") or
                    cmd.is_app("check-sat")
                ): continue

                # Check that all declarations are present in the original query
                # TODO: relax this for skolem constants
                if isinstance(cmd, Application) and len(cmd.args) != 0 and isinstance(cmd.args[0], Atom):
                    if cmd.args[0].name.startswith("declare") or cmd.args[0].name.startswith("define"):
                        if cmd not in original_set:
                            comments.append(f"potential skolem variable {cmd}")
                            write_query(cmd)

            # Then push the negation of conjunction of all assertions in the edited query
            # TODO: assuming that all declarations are still shared
            additional_asserts = tuple(
                cmd.args[1]
                for cmd in edited
                if cmd.is_app("assert") and (
                    # If pruning is enabled, we don't consider common assertions in both files
                    args.no_prune or cmd not in original_set
                )
            )

            if original_goal != edited_goal:
                comments.append("goal edited")

            write_query(Application((
                Atom("assert"),
                Application((
                    Atom("not"),
                    Application((
                        Atom("and"),

                        # If the goal itself is edited, we need to prove that the edited goal => original goal
                        # NOTE: adding another negation here since the goals are already negated
                        Atom("true") if original_goal == edited_goal else
                        Application((
                            Atom("=>"),
                            Application((Atom("not"), edited_goal.args[1])),
                            Application((Atom("not"), original_goal.args[1])),
                        )),

                        # (Optional) to make sure all the trigger terms are still present,
                        # if no_goal is set, we still put in the original goal.
                        # However, this makes the obligation harder to prove.
                        # NOTE: adding another negation here since the goal is already negated
                        Atom("true") if not args.prove_edited_goal else
                        Application((Atom("not"), edited_goal.args[1])),

                        *additional_asserts,
                    )),
                ))
            )))

            write_query(Application((Atom("check-sat"),)))
            new_query.flush()

        # Call Z3 to check if the new_query is unsat
        with status(f"validating {original_path} => {edited_path}"):
            return run_z3(args, new_query.name), comments

def run_job(
    args: argparse.Namespace,
    original_path: str,
    edited_path: str,
):
    with get_output_file(args, "a") as output:
        output_writer = csv.writer(output)
        start = time.time()
        comments = []

        try:
            result, comments = validate_edits(args, original_path, edited_path)
            elapsed = f"{time.time() - start:.2f}"

            output_writer.writerow([
                original_path,
                edited_path,
                "valid" if result == "unsat" else f"invalid: {result}",
                elapsed,
                "; ".join(comments),
            ])
        except Exception as e:
            elapsed = f"{time.time() - start:.2f}"
            eprint(traceback.format_exc())
            output_writer.writerow([original_path, edited_path, f"exception: {e}", elapsed, "; ".join(comments)])

def get_output_file(args: argparse.Namespace, mode: str = "w") -> sys.TextIO:
    if args.output is not None:
        return open(args.output, mode)
    else:
        return sys.stdout

def set_common_arguments(parser: argparse.ArgumentParser):
    parser.add_argument("--no-prune", action="store_true", default=False, help="Do not prune common assertions")
    parser.add_argument("--prove-edited-goal", action="store_true", default=False, help="Also prove edited goal in the resulting query")
    parser.add_argument("--z3", default="z3", help="Path to Z3")
    parser.add_argument("--seed", type=int, default=0, help="Random seed for Z3")
    parser.add_argument("--timeout", type=float, default=5.0, help="Timeout for Z3")
    parser.add_argument("-o", "--output", help="Output CSV file")

def main():
    parser = argparse.ArgumentParser(description="Take queries A and B, and checks whether B unsat ==> A unsat")

    subparsers = parser.add_subparsers(title="subcommand", dest="subcommand", required=True)
    parser_single = subparsers.add_parser("single", help="Validate a single pair of queries")
    parser_batch = subparsers.add_parser("batch", help="Validate a batch of queries")

    # Single mode arguments
    parser_single.add_argument("original", help="The original SMT-LIB 2 file")
    parser_single.add_argument("edited", help="The edited SMT-LIB 2 file")
    parser_single.add_argument("--log-smt", help="Log the generated SMT query to a file")
    set_common_arguments(parser_single)

    # Batch mode arguments
    parser_batch.add_argument("batch", help="A JSON file of the format { <original path>: [ [ <qid>, <edit type>, <edited path> ], ... ], ... }")
    parser_batch.add_argument("-j", "--jobs", type=int, default=1, help="Number of parallel jobs")
    set_common_arguments(parser_batch)

    args = parser.parse_args()

    # Write headers first
    if args.output is None:
        print("original,edited,result,time,comment", flush=True)
    else:
        with open(args.output, "w") as file:
            print("original,edited,result,time,comment", file=file)

    if args.subcommand == "single":
        run_job(args, args.original, args.edited)

    elif args.subcommand == "batch":
        with multiprocessing.Pool(args.jobs) as pool:
            with open(args.batch) as f:
                batch = json.load(f)
                jobs = [
                    (args, original, edit)
                    for original, edits in batch.items() for _, _, edit in edits
                ]

                # Sort the jobs to make it more deterministic
                jobs.sort(key=lambda x: (x[0], x[1]))

                eprint("total jobs:", len(jobs))
                pool.starmap(run_job, jobs)

if __name__ == "__main__":
    main()
