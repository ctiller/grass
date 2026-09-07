"""Falsifying tests for `Tools/shared-imports-sync.py`.

That tool rewrites two files the whole fleet is told to run `--write` on, and
three successive versions of it corrupted content while `--check` reported
success. So the standard here is not "the result looks right".

## Why every case states its exact expected output

The previous version of this file compared two *lists*: the non-import lines,
and the import names. A reviewer then showed that 14 of 17 behaviour-changing
mutations survived it, including two that matter a great deal:

* writing the import block at offset 0 instead of at the first import -- which
  is precisely the historical "a docstring above the imports" bug this file has
  a named case for; and
* writing the block at the end of the file, which Lean rejects outright with
  `invalid 'import' command, it must be used in the beginning of the file`.

Both preserve the set of non-import lines and the list of import names, so a
list comparison cannot see either. Position is the thing that matters, and
bytes are the only way to pin it without writing a second implementation of the
tool and trusting that instead.

So each case carries the exact text it must produce. A mutation that changes
what the tool writes, anywhere, fails here.

`main` is exercised too. Testing only the internals leaves the entry point free
to ignore them, which is the same hole this repository just closed in
`Tools/DocstringAuditSelfTest.py`.

Run: python Tools/SharedImportsSyncSelfTest.py
"""

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
WANTED = ["Grass.Alpha", "Grass.Beta", "Grass.Gamma"]
BLOCK = "".join(f"import {n}{LF}" for n in WANTED)
CRLF_BLOCK = "".join(f"import {n}{CRLF}" for n in WANTED)
TAIL = LF + "def x := 1" + LF

# (name, input, exact expected output)
CASES = [
    (
        "already correct",
        BLOCK + TAIL,
        BLOCK + TAIL,
    ),
    (
        "out of order",
        "import Grass.Gamma" + LF + "import Grass.Alpha" + LF
        + "import Grass.Beta" + LF + TAIL,
        BLOCK + TAIL,
    ),
    (
        "duplicated import",
        "import Grass.Alpha" + LF + "import Grass.Alpha" + LF
        + "import Grass.Beta" + LF + "import Grass.Gamma" + LF + TAIL,
        BLOCK + TAIL,
    ),
    (
        "missing import",
        "import Grass.Alpha" + LF + "import Grass.Gamma" + LF + TAIL,
        BLOCK + TAIL,
    ),
    (
        # The block must land where the first import was, not at offset 0.
        "module docstring above the imports",
        "/-! preamble -/" + LF + "import Grass.Gamma" + LF
        + "import Grass.Alpha" + LF + "import Grass.Beta" + LF + TAIL,
        "/-! preamble -/" + LF + BLOCK + TAIL,
    ),
    (
        "import Lean above the block",
        "import Lean" + LF + "import Grass.Gamma" + LF
        + "import Grass.Alpha" + LF + "import Grass.Beta" + LF + TAIL,
        "import Lean" + LF + BLOCK + TAIL,
    ),
    (
        # A blank line inside the block: the imports consolidate, the blank
        # line survives, and nothing is duplicated.
        "blank line inside the block",
        "import Grass.Alpha" + LF + LF + "import Grass.Gamma" + LF
        + "import Grass.Beta" + LF + TAIL,
        BLOCK + LF + TAIL,
    ),
    (
        "line comment inside the block",
        "import Grass.Alpha" + LF + "-- by layer" + LF
        + "import Grass.Gamma" + LF + "import Grass.Beta" + LF + TAIL,
        BLOCK + "-- by layer" + LF + TAIL,
    ),
    (
        "mixed line endings: only the block follows the first import",
        "import Grass.Gamma" + CRLF + "import Grass.Alpha" + CRLF
        + "def x := 1" + LF + "def y := 2" + LF,
        CRLF_BLOCK + "def x := 1" + LF + "def y := 2" + LF,
    ),
    (
        "no trailing newline",
        "import Grass.Gamma" + LF + "import Grass.Alpha" + LF + "def x := 1",
        BLOCK + "def x := 1",
    ),
    (
        "byte-order mark",
        BOM + "import Grass.Alpha" + LF + "import Grass.Gamma" + LF + TAIL,
        BOM + BLOCK + TAIL,
    ),
]

# Shapes where an import-looking line is not an import. The tool must leave
# every one of these exactly as it found it: the block is already correct, and
# the decoy must neither be counted nor edited.
DECOYS = [
    ("block comment above the block",
     "/- e.g." + LF + "import Grass.Nope" + LF + "-/" + LF),
    ("block comment below the block",
     None),
    ("nested block comment",
     "/- outer /- inner" + LF + "import Grass.Nope" + LF + "-/ out -/" + LF),
    ("doc comment",
     "/-- e.g. `import Grass.Nope` -/" + LF),
    ("line comment naming a block opener",
     "-- keep sorted; the /-! header explains why" + LF),
    ("line comment that is only an opener",
     "--/-" + LF),
    ("string literal holding a block opener",
     'def opener := "/-"' + LF),
    ("string literal holding an import",
     'def sample := "import Grass.Nope"' + LF),
]

# Characters `str.splitlines()` treats as line breaks and `str.split(chr(10))`
# does not. A rewriter built on the former turns each into a newline.
EXOTIC = ["\x0b", "\x0c", "\x1c", "\x1d", "\x1e", "\x85", " ", " ",
          "\r"]


def module_names_are_lean_identifiers() -> list[str]:
    """`modules_on_disk` must refuse a path it cannot spell as an import.

    Stubbed out by every case above, so a reviewer's mutation that dropped the
    check survived the whole file. `Grass/A.B.lean` renders `import Grass.A.B`,
    which parses as a module that does not exist.
    """
    failures = []
    saved = os.getcwd()
    # The chdir is undone *inside* the context manager: on Windows a directory
    # that is some process's cwd cannot be removed, so restoring afterwards
    # makes the cleanup raise.
    with tempfile.TemporaryDirectory() as raw:
        try:
            os.chdir(raw)
            os.makedirs("Grass")
            io.open(os.path.join("Grass", "Fine.lean"), "w").write("")
            if sync.modules_on_disk() != ["Grass.Fine"]:
                failures.append(
                    "modules_on_disk did not read an ordinary tree correctly")
            io.open(os.path.join("Grass", "A.B.lean"), "w").write("")
            try:
                sync.modules_on_disk()
                failures.append(
                    "modules_on_disk accepted Grass/A.B.lean, which renders "
                    "an import of a module that cannot exist")
            except SystemExit:
                pass
        finally:
            os.chdir(saved)
    return failures



def run(text, expected, name):
    with tempfile.TemporaryDirectory() as raw:
        path = os.path.join(raw, "Registry.lean")
        io.open(path, "w", encoding="utf-8", newline="").write(text)
        try:
            sync.process(path, WANTED, write=True)
        except SystemExit as exit_error:
            return [f"{name}: refused ({exit_error}) a file it should rewrite"]
        after = io.open(path, encoding="utf-8", newline="").read()
        if after != expected:
            return [f"{name}: wrong output.{LF}      expected {expected!r}"
                    f"{LF}      got      {after!r}"]
        # Running again must change nothing.
        sync.process(path, WANTED, write=True)
        again = io.open(path, encoding="utf-8", newline="").read()
    if again != expected:
        return [f"{name}: not idempotent.{LF}      second run {again!r}"]
    return []


def main() -> int:
    failures = []
    for name, text, expected in CASES:
        failures.extend(run(text, expected, name))

    for name, decoy in DECOYS:
        # `None` means "put the decoy after the block" rather than before
        # it; position matters, because only a decoy above the block can
        # capture the insertion point.
        body = (BLOCK + LF + "/- e.g." + LF + "import Grass.Nope" + LF
                + "-/" + LF) if decoy is None else decoy + BLOCK
        failures.extend(run(body, body, "decoy: " + name))

    for char in EXOTIC:
        text = BLOCK + 'def s := "a' + char + 'b"' + LF
        failures.extend(
            run(text, text, "exotic break %r must survive" % char))

    # A file with no real import must be refused, not guessed at, and not
    # touched.
    with tempfile.TemporaryDirectory() as raw:
        path = os.path.join(raw, "Registry.lean")
        original = "/- import Grass.Alpha -/" + LF + TAIL
        io.open(path, "w", encoding="utf-8", newline="").write(original)
        try:
            sync.process(path, WANTED, write=True)
            failures.append(
                "a registry whose only import is inside a comment was "
                "rewritten rather than refused")
        except SystemExit:
            if io.open(path, encoding="utf-8", newline="").read() != original:
                failures.append("refused that registry but wrote to it anyway")

    failures.extend(module_names_are_lean_identifiers())
    failures.extend(main_reports_drift())

    if failures:
        print("shared-imports-sync self-test: FAILED\n")
        for failure in failures:
            sys.stdout.buffer.write(("  " + failure).encode("utf-8", "replace")
                                    + b"\n")
        return 1
    print(f"shared-imports-sync self-test: {len(CASES)} rewrites, "
          f"{len(DECOYS)} decoys and {len(EXOTIC)} exotic line breaks, "
          "each byte-exact")
    return 0


def main_reports_drift() -> list[str]:
    """`main` must exit 1 on drift and 0 when clean.

    Testing `process` alone leaves `main` free to ignore what it returns.
    """
    import contextlib
    failures = []
    saved = (sync.TARGETS, sync.modules_on_disk)
    sink = io.TextIOWrapper(io.BytesIO(), encoding="utf-8")
    try:
        with tempfile.TemporaryDirectory() as raw:
            path = os.path.join(raw, "Registry.lean")
            io.open(path, "w", encoding="utf-8", newline="").write(
                "import Grass.Alpha" + LF + TAIL)
            sync.TARGETS = (path,)
            sync.modules_on_disk = lambda: list(WANTED)
            with contextlib.redirect_stdout(sink):
                drifted = sync.main(["prog"])
                sync.main(["prog", "--write"])
                clean = sync.main(["prog"])
            if drifted != 1:
                failures.append(
                    f"main() returned {drifted} on a registry missing two "
                    "imports; the check would pass on drift")
            if clean != 0:
                failures.append(
                    f"main() returned {clean} after --write fixed the file; a "
                    "gate that fails when clean gets switched off")
    finally:
        sync.TARGETS, sync.modules_on_disk = saved
    return failures


if __name__ == "__main__":
    sys.exit(main())
