"""
A script to validate query edits (e.g., instantiations and erasures of quantifiers).
"""

from __future__ import annotations

from dataclasses import dataclass

import os
import sys
sys.setrecursionlimit(10000) # For parsing SMT queries

import json
import argparse
import tempfile
import traceback
import subprocess
import multiprocessing

class Exp: ...

@dataclass(frozen=True)
class Application(Exp):
    args: tuple[Exp]

    def __str__(self):
        return f"({' '.join(map(str, self.args))})"

    def is_app(self, name: str) -> bool:
        return len(self.args) != 0 and self.args[0] == Atom(name)

    def normalize(self) -> Application:
        """
        Apply some custom normalization rules, such as removing :qid and :skolemid, and :name
        """
        if self.is_app("!"):
            new_args = []
            i = 0

            while i < len(self.args):
                arg = self.args[i]
                if arg in (Atom(":named"), Atom(":qid"), Atom(":skolemid"), Atom(":weight")):
                    i += 2
                else:
                    new_args.append(arg.normalize())
                    i += 1

            return Application(tuple(new_args))

        else:
            return Application(tuple(arg.normalize() for arg in self.args))

@dataclass(frozen=True)
class Atom(Exp):
    name: str

    def __str__(self):
        return self.name

    def is_app(self, _: str) -> bool:
        return False

    def normalize(self) -> Atom:
        return self

def tokenize_smtlib2(s: str) -> list[tuple[int, str]]:
    """
    A simple tokenizer for SMT-LIB 2
    Return a list of tokens (with comments ignored)
    """

    tokens = [] # (position, token)
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
                tokens.append((string_start, string_buffer + c))
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
                tokens.append((i, c))
                i += 1
            elif c.isspace():
                # Skip all whitespaces
                i += len(s[i:]) - len(s[i:].lstrip())
            elif c == '"':
                in_string = True
                string_start = i
                string_buffer = c
                i += 1
            else:
                # Take characters until space or ( or )
                old_i = i
                while i < len(s) and s[i] != "(" and s[i] != ")" and not s[i].isspace():
                    i += 1
                tokens.append((old_i, s[old_i:i]))

    return tokens

def parse_smtlib2(file_path: str) -> list[Exp]:
    """
    Parse an SMT-LIB 2 query
    """

    top_level = []

    # Stack record a nested list of unclosed applications
    stack = []

    with open(file_path) as f:
        # TODO: assuming string literals do not include newlines

        for line_num, line in enumerate(f):
            for pos, token in tokenize_smtlib2(line):
                if token == "(":
                    stack.append([])

                elif token == ")":
                    assert len(stack) != 0, f"{file_path}:{line_num}:{pos}: unexpected ')'"

                    exp = Application(tuple(stack.pop()))
                    if len(stack) == 0:
                        top_level.append(exp)
                    else:
                        stack[-1].append(exp)

                else:
                    assert len(stack) != 0, f"{file_path}:{line_num}:{pos}: atoms can not be at the top level"
                    stack[-1].append(Atom(token))

    return top_level

def supports_color():
    """
    Returns True if the running system's terminal supports color, and False
    otherwise.
    """
    plat = sys.platform
    supported_platform = plat != "Pocket PC" and (plat != "win32" or
                                                  "ANSICON" in os.environ)
    is_a_tty = (
        hasattr(sys.stdout, "isatty") and sys.stdout.isatty() and
        hasattr(sys.stderr, "isatty") and sys.stderr.isatty()
    )
    return supported_platform and is_a_tty

def eprint(*args) -> None:
    print(*args, file=sys.stderr, flush=True)

def eprint_status(msg: str) -> None:
    if supports_color():
        print(f"\033[2K\r{msg}", file=sys.stderr, end="", flush=True)

def validate_edits(
    original_path: str,
    edited_path: str,
    args: argparse.Namespace,
) -> None:
    try:
        eprint_status(f"parsing original {original_path}...")
        original = parse_smtlib2(original_path)

        eprint_status(f"parsing edited {edited_path}...")
        edited = parse_smtlib2(edited_path)

        # Normalize all expressions
        original = [ cmd.normalize() for cmd in original ]
        edited = [ cmd.normalize() for cmd in edited ]

        # Remove the last assertion (goal assertion) in both queries
        # Later we also check that edited_goal => original_goal if they are different
        original_goal = None
        edited_goal = None

        for i in range(len(original) - 1, -1, -1):
            if original[i].is_app("assert"):
                original_goal = original.pop(i)
                break

        for i in range(len(edited) - 1, -1, -1):
            if edited[i].is_app("assert"):
                edited_goal = edited.pop(i)
                break

        assert original_goal is not None, "no goal assertion found in the original query"
        assert edited_goal is not None, "no goal assertion found in the edited query"

        original_cmd_set = set(original)
        original_assert_set = { cmd.args[1] for cmd in original if cmd.is_app("assert") }

        with (
            tempfile.NamedTemporaryFile(mode="w", suffix=".smt2")
            if not hasattr(args, "log_smt") or args.log_smt is None else open(args.log_smt, "w")
        ) as new_query:
            eprint_status("generating new query...")

            # Override set-option's
            print("(set-option :auto_config false)", file=new_query)
            print("(set-option :smt.mbqi false)", file=new_query)

            # First push all commands in the original query, but skip some commands (e.g. push, pop, set-option)
            push_count = 0
            pop_count = 0
            check_sat_count = 0
            for cmd in original:
                if cmd.is_app("push"):
                    push_count += 1
                    assert push_count <= 1, "multiple push commands found"
                    continue

                if cmd.is_app("pop"):
                    pop_count += 1
                    assert pop_count <= 1, "multiple pop commands found"
                    continue

                if cmd.is_app("set-option") or cmd.is_app("set-info"):
                    continue

                if cmd.is_app("check-sat"):
                    check_sat_count += 1
                    assert check_sat_count <= 1, "multiple check-sat commands found"
                    continue

                print(cmd, file=new_query)

            assert check_sat_count != 0, "no check-sat command found in the original query"

            push_count = 0
            pop_count = 0
            check_sat_count = 0
            for cmd in edited:
                if cmd.is_app("push"):
                    push_count += 1
                    assert push_count <= 1, "multiple push commands found"
                    continue

                if cmd.is_app("pop"):
                    pop_count += 1
                    assert pop_count <= 1, "multiple pop commands found"
                    continue

                if cmd.is_app("set-option") or cmd.is_app("set-info"):
                    continue

                if cmd.is_app("check-sat"):
                    check_sat_count += 1
                    assert check_sat_count <= 1, "multiple check-sat commands found"
                    continue

                # Check that all declarations are present in the original query
                # TODO: relax this for skolem constants
                if isinstance(cmd, Application) and len(cmd.args) != 0 and isinstance(cmd.args[0], Atom):
                    if cmd.args[0].name.startswith("declare") or cmd.args[0].name.startswith("define"):
                        # assert cmd in original_cmd_set, f"declaration {cmd} not found in the original query"
                        if cmd not in original_cmd_set:
                            eprint(f"[warning] declaration {cmd} not found in the original query ({original_path} => {edited_path})")
                            print(cmd, file=new_query)

            assert check_sat_count != 0, "no check-sat command found in the edited query"

            # Then push the negation of conjunction of all assertions in the edited query
            # TODO: assuming that all declarations are still shared
            additional_asserts = tuple(
                cmd.args[1]
                for cmd in edited
                if cmd.is_app("assert") and len(cmd.args) == 2 and (
                    # If pruning is enabled, we don't consider common assertions in both files
                    args.no_prune or cmd.args[1] not in original_assert_set
                )
            )

            if original_goal != edited_goal:
                eprint(f"[warning] goal is edited ({original_path} => {edited_path})")

            print(Application((
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
            )), file=new_query)

            print(Application((Atom("check-sat"),)), file=new_query)
            new_query.flush()

            # Call Z3 to check if the new_query is unsat
            eprint_status(f"validaing {original_path} => {edited_path}...")

            try:
                result = subprocess.run(
                    [args.z3, new_query.name],
                    stdout=subprocess.PIPE,
                    stderr=sys.stderr,
                    timeout=args.timeout,
                    text=True,
                )
                if result.returncode == 0 and result.stdout.strip() == "unsat":
                    eprint_status("")
                    eprint(f"{original_path} => {edited_path}: valid")
                    return True
                else:
                    eprint_status("")
                    eprint(f"{original_path} => {edited_path}: invalid: {result.stdout.strip()}")
                    return False

            except subprocess.TimeoutExpired:
                eprint_status("")
                eprint(f"{original_path} => {edited_path}: timeout")
                return False
    except Exception as e:
        eprint_status("")
        eprint(traceback.format_exc())
        eprint(f"{original_path} => {edited_path}: exception: {e}")
        return False

def set_common_arguments(parser: argparse.ArgumentParser):
    parser.add_argument("--no-prune", action="store_true", default=False, help="Do not prune common assertions")
    parser.add_argument("--prove-edited-goal", action="store_true", default=False, help="Also prove edited goal in the resulting query")
    parser.add_argument("--z3", default="z3", help="Path to Z3")
    parser.add_argument("--timeout", type=float, default=5.0, help="Timeout for Z3")

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

    if args.subcommand == "single":
        validate_edits(args.original, args.edited, args)

    elif args.subcommand == "batch":
        with multiprocessing.Pool(args.jobs) as pool:
            with open(args.batch) as f:
                batch = json.load(f)

                jobs = [ (original, edit, args) for original, edits in batch.items() for _, _, edit in edits ]

                # Sort the jobs to make it more deterministic
                jobs.sort(key=lambda x: (x[0], x[1]))

                eprint("total jobs:", len(jobs))
                pool.starmap(validate_edits, jobs)

if __name__ == "__main__":
    main()
