"""Falsifying tests for `Tools/shared-imports-sync.py`.

Every case here is a file shape that made the first version of that tool destroy
content while reporting success. A cold reviewer found all four inside one
session, which is the reason this file exists: the tool rewrites files that the
whole fleet is instructed to run `--write` on, so "it looked right" is not a
standard it can be held to.

The invariant under test is narrow and total: **the tool may reorder, add and
remove `import Grass.` lines, and may change nothing else.** Each case asserts
that the non-import content survives byte-for-byte.

Run: python Tools/SharedImportsSyncSelfTest.py
"""

import importlib.util
import io
import os
import re
import sys
import tempfile
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "shared_imports_sync", Path(__file__).with_name("shared-imports-sync.py"))
sync = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(sync)

LF = "\n"
CRLF = "\r\n"

BODY = [
    "",
    "/-!",
    "# A registry",
    "-/",
    "",
    "open Lean in",
    "run_cmd do",
    "  pure ()",
]

WANTED = ["Grass.Alpha", "Grass.Beta", "Grass.Gamma"]


def build(imports: list[str], newline: str, header: list[str] | None = None,
          body: list[str] | None = None) -> str:
    lines = (header if header is not None else ["import Lean"])
    lines = lines + imports + (body if body is not None else BODY)
    return newline.join(lines) + newline


# The test's own parser, deliberately not the tool's. Verifying a rewriter
# with the rewriter's own reader hides exactly the bugs that matter: when the
# leading-run parser was reintroduced as a mutation, every case still passed,
# because both the tool and the check agreed to stop reading at the same wrong
# place. The result was a file carrying a duplicate import that neither could
# see.
IMPORT_RE = re.compile(r"^import\s+Grass\.[A-Za-z0-9_.']*\s*$")


def non_import_lines(text: str) -> list[str]:
    return [line for line in text.splitlines() if not IMPORT_RE.match(line)]


def import_names(text: str) -> list[str]:
    return [line.split()[1] for line in text.splitlines()
            if IMPORT_RE.match(line)]


CASES = []


def case(name):
    def register(fn):
        CASES.append((name, fn))
        return fn
    return register


@case("one CRLF line in an LF file (deleted every declaration)")
def _crlf_mix():
    text = build(["import Grass.Alpha", "import Grass.Gamma"], LF)
    return text.replace("import Grass.Alpha" + LF,
                        "import Grass.Alpha" + CRLF, 1)


@case("a blank line inside the block (produced 53 duplicates)")
def _blank_inside():
    return build(["import Grass.Alpha", "", "import Grass.Gamma"], LF)


@case("a comment inside the block")
def _comment_inside():
    return build(["import Grass.Alpha", "-- grouped by layer",
                  "import Grass.Gamma"], LF)


@case("a docstring above the imports (block written before it)")
def _docstring_first():
    return build(["import Grass.Alpha", "import Grass.Gamma"], LF,
                 header=["/-! preamble -/", "import Lean"])


@case("already correct, CRLF throughout")
def _crlf_clean():
    return build([f"import {n}" for n in WANTED], CRLF)


@case("out of order only")
def _unsorted():
    return build(["import Grass.Gamma", "import Grass.Alpha",
                  "import Grass.Beta"], LF)


@case("duplicated import")
def _duplicated():
    return build(["import Grass.Alpha", "import Grass.Alpha",
                  "import Grass.Beta", "import Grass.Gamma"], LF)


def run_case(name, text: str) -> list[str]:
    failures = []
    before = non_import_lines(text)
    with tempfile.TemporaryDirectory() as raw:
        path = os.path.join(raw, "Registry.lean")
        io.open(path, "w", encoding="utf-8", newline="").write(text)
        try:
            sync.process(path, WANTED, write=True)
        except SystemExit as exit_error:
            # Refusing beats destroying, but every shape here is a legitimate
            # file the tool is supposed to fix, so a refusal is still a
            # failure -- and accepting it once let a reintroduced parser bug
            # survive this very test.
            after_text = io.open(path, encoding="utf-8", newline="").read()
            failures.append(
                f"{name}: the tool refused ({exit_error}) instead of "
                "rewriting a legitimate file")
            if after_text != text:
                failures.append(
                    f"{name}: and it had already modified the file")
            return failures
        after_text = io.open(path, encoding="utf-8", newline="").read()

    after = non_import_lines(after_text)
    if after != before:
        failures.append(
            f"{name}: non-import content changed.\n"
            f"      before: {before!r}\n"
            f"      after:  {after!r}")
    found = import_names(after_text)
    if found != WANTED:
        failures.append(
            f"{name}: import block is {found!r}, expected {WANTED!r}")
    # Running again must be a no-op.
    with tempfile.TemporaryDirectory() as raw:
        path = os.path.join(raw, "Registry.lean")
        io.open(path, "w", encoding="utf-8", newline="").write(after_text)
        sync.process(path, WANTED, write=True)
        if io.open(path, encoding="utf-8", newline="").read() != after_text:
            failures.append(f"{name}: a second --write changed the file again")
    return failures


def main() -> int:
    failures: list[str] = []
    for name, make in CASES:
        failures.extend(run_case(name, make()))

    # A file with no library imports at all must be refused, not guessed at.
    with tempfile.TemporaryDirectory() as raw:
        path = os.path.join(raw, "Registry.lean")
        original = build([], LF)
        io.open(path, "w", encoding="utf-8", newline="").write(original)
        try:
            sync.process(path, WANTED, write=True)
            failures.append(
                "a registry with no library imports was rewritten rather than "
                "refused; the tool would be guessing where the block goes")
        except SystemExit:
            if io.open(path, encoding="utf-8", newline="").read() != original:
                failures.append(
                    "refused a registry with no library imports but wrote to "
                    "it anyway")

    if failures:
        print("shared-imports-sync self-test: FAILED\n")
        for failure in failures:
            print("  " + failure)
        return 1
    print(f"shared-imports-sync self-test: {len(CASES)} file shapes, "
          "non-import content preserved in each")
    return 0


if __name__ == "__main__":
    sys.exit(main())
