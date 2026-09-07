"""Falsifying tests for `Tools/shared-imports-sync.py`.

That tool rewrites two files the whole fleet is told to run `--write` on. Four
versions of it corrupted content while `--check` reported success, so the bar
here is not "the result looks right".

Every case states the exact bytes the tool must produce, or states that it must
refuse and leave the file untouched. Lists of lines are not enough: comparing
"the non-import lines" and "the import names" let a reviewer land the block at
offset 0 -- the historical bug this file has a named case for -- and at end of
file, which Lean rejects outright. Both preserve those lists.

`REFUSALS` matter as much as the rewrites. A tool that bails out on a file it
does not understand is safe; one that guesses is what produced every incident
here.

Every shape below is one a cold reviewer used successfully against some version
of the tool. They are kept after the fix, because the fixes have been wrong
before.

Run: python Tools/SharedImportsSyncSelfTest.py
"""

import contextlib
import importlib.util
import io
import os
import sys
import tempfile
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "shared_imports_sync", Path(__file__).with_name("shared-imports-sync.py"))
sync = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(sync)

LF = "\n"
CRLF = "\r\n"
BOM = "﻿"
W = ["Grass.Alpha", "Grass.Beta", "Grass.Gamma"]
BLOCK = "".join(f"import {n}{LF}" for n in W)
CRLF_BLOCK = "".join(f"import {n}{CRLF}" for n in W)
# A Lean `Char` literal holding a double quote. This desynchronised a
# whole-file scanner and let the block be written inside a string literal.
DQ = "def dq : Char := '" + '"' + "'" + LF

REWRITES = [
    ("already correct", BLOCK + "def x := 1" + LF, BLOCK + "def x := 1" + LF),
    ("out of order",
     "import Grass.Gamma" + LF + "import Grass.Alpha" + LF
     + "import Grass.Beta" + LF + "def x := 1" + LF,
     BLOCK + "def x := 1" + LF),
    ("duplicated import",
     "import Grass.Alpha" + LF + "import Grass.Alpha" + LF
     + "import Grass.Beta" + LF + "import Grass.Gamma" + LF + "def x := 1" + LF,
     BLOCK + "def x := 1" + LF),
    ("missing import",
     "import Grass.Alpha" + LF + "import Grass.Gamma" + LF + "def x := 1" + LF,
     BLOCK + "def x := 1" + LF),
    # Position: the block belongs where the first import was.
    ("module docstring above the imports",
     "/-! preamble -/" + LF + "import Grass.Gamma" + LF
     + "import Grass.Alpha" + LF + "import Grass.Beta" + LF + "def x := 1" + LF,
     "/-! preamble -/" + LF + BLOCK + "def x := 1" + LF),
    ("import Lean above the block",
     "import Lean" + LF + "import Grass.Gamma" + LF + "import Grass.Alpha" + LF
     + "import Grass.Beta" + LF + "def x := 1" + LF,
     "import Lean" + LF + BLOCK + "def x := 1" + LF),
    ("blank line inside the block",
     "import Grass.Alpha" + LF + LF + "import Grass.Gamma" + LF
     + "import Grass.Beta" + LF + "def x := 1" + LF,
     BLOCK + LF + "def x := 1" + LF),
    # An annotated import is recognised, so the list reads as already correct
    # and the annotation survives. An earlier version could not see the line
    # and duplicated the import beneath itself.
    ("trailing line comment on an import is kept",
     "import Grass.Alpha" + LF + "import Grass.Beta  -- the core layer" + LF
     + "import Grass.Gamma" + LF + "def x := 1" + LF,
     "import Grass.Alpha" + LF + "import Grass.Beta  -- the core layer" + LF
     + "import Grass.Gamma" + LF + "def x := 1" + LF),
    ("an annotated import still counts when the list is wrong",
     "import Grass.Gamma  -- last" + LF + "import Grass.Alpha" + LF
     + "def x := 1" + LF,
     BLOCK + "def x := 1" + LF),
    ("mixed line endings follow the first import",
     "import Grass.Gamma" + CRLF + "import Grass.Alpha" + CRLF
     + "import Grass.Beta" + CRLF + "def x := 1" + LF + "def y := 2" + LF,
     CRLF_BLOCK + "def x := 1" + LF + "def y := 2" + LF),
    ("no trailing newline",
     "import Grass.Gamma" + LF + "import Grass.Alpha" + LF
     + "import Grass.Beta" + LF + "def x := 1",
     BLOCK + "def x := 1"),
    ("byte-order mark",
     BOM + "import Grass.Alpha" + LF + "import Grass.Gamma" + LF
     + "def x := 1" + LF,
     BOM + BLOCK + "def x := 1" + LF),
    # Everything after the header is data, and must not be examined at all.
    ("char literal and a string holding an import, after the header",
     "import Grass.Alpha" + LF + DQ + 'def shape : String := "eg:' + LF
     + "import Grass.Beta" + LF + '"' + LF,
     BLOCK + DQ + 'def shape : String := "eg:' + LF + "import Grass.Beta" + LF
     + '"' + LF),
    ("raw string ending in a backslash",
     "import Grass.Alpha" + LF + 'def raw := r"C:' + chr(92) + '"' + LF
     + 'def s := "import Grass.Nope"' + LF,
     BLOCK + 'def raw := r"C:' + chr(92) + '"' + LF
     + 'def s := "import Grass.Nope"' + LF),
]

# Shapes that must come back byte-identical: the block is already correct and
# the import-looking line is a decoy the tool must not count or edit.
DECOYS = [
    ("block comment above the block",
     "/- e.g." + LF + "import Grass.Nope" + LF + "-/" + LF + BLOCK),
    ("nested block comment above the block",
     "/- a /- b" + LF + "import Grass.Nope" + LF + "-/ c -/" + LF + BLOCK),
    ("doc comment above the block",
     "/-- e.g." + LF + "import Grass.Nope" + LF + "-/" + LF + BLOCK),
    ("line comment naming a block opener",
     "-- sorted; the /-! header explains why" + LF + BLOCK),
    ("line comment that is only an opener", "--/-" + LF + BLOCK),
    ("block comment below the block",
     BLOCK + LF + "/- e.g." + LF + "import Grass.Nope" + LF + "-/" + LF),
    ("string literal holding an import, below the header",
     BLOCK + 'def s := "import Grass.Nope"' + LF),
    ("form feed in a later string", BLOCK + 'def s := "a\x0cb"' + LF),
    ("U+2028 in a later string", BLOCK + 'def s := "a b"' + LF),
    ("lone carriage return in a later string",
     BLOCK + 'def s := "a\rb"' + LF),
]

# Files the tool must refuse outright, leaving them untouched.
REFUSALS = [
    ("no import in the header, only inside a string",
     DQ + 'def shape : String := "reads:' + LF + "import Grass.Alpha" + LF
     + '"' + LF),
    ("no import at all", "def x := 1" + LF),
    ("unterminated comment before the block", "/- oops" + LF + BLOCK),
    ("whole file is a comment", "/- everything" + LF + BLOCK + "still" + LF),
]


def rewrite_case(name, text, expected):
    with tempfile.TemporaryDirectory() as raw:
        path = os.path.join(raw, "R.lean")
        io.open(path, "w", encoding="utf-8", newline="").write(text)
        try:
            sync.process(path, W, write=True)
        except SystemExit as exit_error:
            return [f"{name}: refused ({exit_error}) a file it should rewrite"]
        after = io.open(path, encoding="utf-8", newline="").read()
        if after != expected:
            return [f"{name}: wrong output.{LF}      expected {expected!r}"
                    f"{LF}      got      {after!r}"]
        sync.process(path, W, write=True)
        again = io.open(path, encoding="utf-8", newline="").read()
    if again != expected:
        return [f"{name}: not idempotent; second run gave {again!r}"]
    return []


def refusal_case(name, text):
    with tempfile.TemporaryDirectory() as raw:
        path = os.path.join(raw, "R.lean")
        io.open(path, "w", encoding="utf-8", newline="").write(text)
        try:
            sync.process(path, W, write=True)
            refused = False
        except SystemExit:
            refused = True
        after = io.open(path, encoding="utf-8", newline="").read()
    problems = []
    if not refused:
        problems.append(f"{name}: rewritten rather than refused")
    if after != text:
        problems.append(f"{name}: modified a file it should not touch")
    return problems


def module_discovery() -> list[str]:
    """`modules_on_disk` must recurse, and must reject unspellable paths.

    The nested module is load-bearing: with only a top-level file here, a
    reviewer's `rglob` -> `glob` mutation went undetected, and that one
    character would strip every nested module from both registries.
    """
    problems = []
    saved = os.getcwd()
    with tempfile.TemporaryDirectory() as raw:
        try:
            os.chdir(raw)
            os.makedirs(os.path.join("Grass", "Sub", "Deep"))
            for rel in [("Grass", "Top.lean"),
                        ("Grass", "Sub", "Mid.lean"),
                        ("Grass", "Sub", "Deep", "Leaf.lean")]:
                io.open(os.path.join(*rel), "w").write("")
            found = sync.modules_on_disk()
            expected = ["Grass.Sub.Deep.Leaf", "Grass.Sub.Mid", "Grass.Top"]
            if found != expected:
                problems.append(
                    f"modules_on_disk returned {found}, expected {expected}; "
                    "it must recurse into subdirectories, or every nested "
                    "module silently leaves both registries")
            io.open(os.path.join("Grass", "A.B.lean"), "w").write("")
            try:
                sync.modules_on_disk()
                problems.append(
                    "modules_on_disk accepted Grass/A.B.lean, which renders "
                    "an import of a module that cannot exist")
            except SystemExit:
                pass
        finally:
            os.chdir(saved)
    return problems


def main_reports_drift() -> list[str]:
    """`main` must exit 1 on drift and 0 when clean, and must rewrite."""
    problems = []
    saved = (sync.TARGETS, sync.modules_on_disk)
    sink = io.TextIOWrapper(io.BytesIO(), encoding="utf-8")
    try:
        with tempfile.TemporaryDirectory() as raw:
            path = os.path.join(raw, "R.lean")
            io.open(path, "w", encoding="utf-8", newline="").write(
                "import Grass.Alpha" + LF + "def x := 1" + LF)
            sync.TARGETS = (path,)
            sync.modules_on_disk = lambda: list(W)
            with contextlib.redirect_stdout(sink):
                drifted = sync.main(["prog"])
                sync.main(["prog", "--write"])
                clean = sync.main(["prog"])
            after = io.open(path, encoding="utf-8", newline="").read()
            if drifted != 1:
                problems.append(
                    f"main() returned {drifted} on a registry missing two "
                    "imports; the check would pass on drift")
            if after != BLOCK + "def x := 1" + LF:
                problems.append(f"main --write produced {after!r}")
            if clean != 0:
                problems.append(
                    f"main() returned {clean} on a clean registry; a gate that "
                    "fails when clean gets switched off")
    finally:
        sync.TARGETS, sync.modules_on_disk = saved
    return problems


def guards_that_only_fire_on_bad_input() -> list[str]:
    """The refusals that no ordinary case can reach.

    Each of these is a guard whose whole job is to stop a wrong run, so no
    rewrite case exercises it and a reviewer's mutation deleting it survived
    the rest of this file.
    """
    problems = []

    # An empty library tree must not produce an empty import list.
    saved = os.getcwd()
    with tempfile.TemporaryDirectory() as raw:
        try:
            os.chdir(raw)
            os.makedirs("Grass")
            try:
                sync.modules_on_disk()
                problems.append(
                    "modules_on_disk accepted a Grass/ with no .lean files; "
                    "--write would then empty both registries")
            except SystemExit:
                pass
        finally:
            os.chdir(saved)

    # `verify` is the last thing between a mis-parse and a damaged file, so it
    # is exercised directly rather than only through a correct rewrite.
    spans = [(0, len("import Grass.Alpha" + LF), "Grass.Alpha")]
    before = "import Grass.Alpha" + LF + "def x := 1" + LF
    for name, after in [
        ("a lost tail", BLOCK),
        ("a changed prefix", "-- added" + LF + BLOCK + "def x := 1" + LF),
        ("a missing import", "import Grass.Alpha" + LF + "def x := 1" + LF),
    ]:
        if sync.verify(before, after, spans, W) is None:
            problems.append(
                f"verify() accepted {name}; it is the only check standing "
                "between a mis-parse and a corrupted registry")
    if sync.verify(before, BLOCK + "def x := 1" + LF, spans, W) is not None:
        problems.append("verify() rejected a correct rewrite")

    # An unrecognised argument must stop, not silently check.
    try:
        sync.main(["prog", "--wrote"])
        problems.append(
            "main accepted --wrote; a typo for --write would silently check "
            "instead of writing and be read as success")
    except SystemExit as exit_error:
        if exit_error.code in (0, None):
            problems.append("main exited 0 on an unknown argument")
    return problems



def main() -> int:
    failures = []
    for name, text, expected in REWRITES:
        failures.extend(rewrite_case(name, text, expected))
    for name, text in DECOYS:
        failures.extend(rewrite_case("decoy: " + name, text, text))
    for name, text in REFUSALS:
        failures.extend(refusal_case("refusal: " + name, text))
    failures.extend(module_discovery())
    failures.extend(main_reports_drift())
    failures.extend(guards_that_only_fire_on_bad_input())

    if failures:
        print("shared-imports-sync self-test: FAILED\n")
        for failure in failures:
            sys.stdout.buffer.write(("  " + failure).encode("utf-8", "replace")
                                    + b"\n")
        return 1
    print(f"shared-imports-sync self-test: {len(REWRITES)} rewrites, "
          f"{len(DECOYS)} decoys and {len(REFUSALS)} refusals, each byte-exact")
    return 0


if __name__ == "__main__":
    sys.exit(main())
