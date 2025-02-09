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

import pyparsing as pp

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

def smtlib2_parser():
    pp.ParserElement.setDefaultWhitespaceChars(" \t\r\n")

    comment = pp.Regex(r";[^\n]*").suppress()

    exp = pp.Forward()

    # String literal
    string_literal = pp.QuotedString('"', escChar='\\', unquoteResults=False)
    string_literal.setParseAction(lambda tokens: Atom(tokens[0]))

    # Symbol
    symbol = pp.Word(pp.alphanums + "+-*/_=<>!?:|.%$&@#'")
    symbol.setParseAction(lambda tokens: Atom(tokens[0]))

    # Application
    app = pp.Group(pp.Suppress("(") + pp.ZeroOrMore(exp) + pp.Suppress(")"))
    app.setParseAction(lambda tokens: Application(tuple(tokens[0])))
    exp <<= string_literal | symbol | app
    exp.ignore(comment)

    exps = pp.OneOrMore(exp)

    return exps

SMTLIB2_PARSER = smtlib2_parser()
del smtlib2_parser

def parse_smtlib2(file_path: str) -> list[Exp]:
    return SMTLIB2_PARSER.parseFile(file_path, parseAll=True)

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

        # If no_goal is set, remove the last assertion in both queries
        # (assuming they are equal)
        original_goal = None
        edited_goal = None
        if args.no_goal:
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
            assert original_goal == edited_goal, "goal assertions are not equal"

        original_cmd_set = set(original)
        original_assert_set = { cmd.args[1] for cmd in original if cmd.is_app("assert") }

        with (
            tempfile.NamedTemporaryFile(mode="w", suffix=".smt2")
            if args.log_smt is None else open(args.log_smt, "w")
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
                    not args.prune or cmd.args[1] not in original_assert_set
                )
            )
            print(Application((
                Atom("assert"),
                Application((
                    Atom("not"),
                    Application((
                        Atom("and"),
                        # To make sure all the trigger terms are still present,
                        # if no_goal is set, we still put in the original goal
                        Application((Atom("not"), original_goal.args[1])),

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
    parser.add_argument("--prune", action="store_true", default=False, help="Prune common assertions")
    parser.add_argument("--no-goal", action="store_true", default=False, help="Do not include the last assertion")
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
