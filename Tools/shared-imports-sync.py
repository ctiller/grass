"""Keep the shared audit registries' import lists equal to the tree.

`Tools/DeclNames.lean` and `Tools/AxiomAudit.lean` each have to import every
module in the build: a name the declaration list cannot see is a name
`Tools/DocstringAudit.py` reports as invented, and a module the axiom audit
cannot see is a module whose axioms nobody counted. Both lists were maintained
by hand, which drifted, and both files sit in one agent's exclusive scope, which
made every other agent queue behind that one to add a line. The import must land
in the same commit as the module it names, because `lake env lean` resolves
imports against the current tree and an import of a module that is not there yet
fails outright for everyone.

So: any agent adding a module runs this with `--write` in the same commit.

## Why this is written the way it is

Two earlier versions corrupted files while `--check` reported success, in six
distinct file shapes between them. Both were built the same way -- split the
file into lines, decide which lines are imports, rebuild the file from lines --
and every defect came from that shape:

* a leading-run parser stopped at the first non-import line, so a blank line, a
  line comment or a module docstring hid imports; and one CRLF line in an
  otherwise-LF file made the whole remainder of the file parse as a single
  import, deleting every declaration in `Tools/AxiomAudit.lean`;
* reading imports from anywhere fixed that and broke something worse. A block
  comment holding an example `import Grass.X` line -- a shape that was sitting
  in `Tools/DeclNames.lean` at the time -- was read as real, and when it sat
  above the real block the imports were rewritten *into the comment*, leaving a
  registry that imported nothing;
* tracking block comments fixed those and left line comments and string
  literals: one `-- ... /-! ...` line opened a block comment that never closed,
  hiding every import after it, which `--write` then re-added as 56 duplicates;
* and underneath all of them `str.splitlines()` also splits on \\v, \\f,
  \\x1c-\\x1e, \\x85, U+2028 and U+2029, so rejoining turned each of those
  characters into a newline and silently edited string literals.

Each fix was asserted with a re-parse "fixpoint" that ran the same reader on
both sides, so it only ever established that the tool was self-consistent.

This version does not rebuild the file. It locates the byte span of each real
import line and splices, so every other byte survives by construction rather
than by reassembly. That is a claim about strings, so it is checked as one:
`strip_imports` of the rewritten text must equal `strip_imports` of the
original, and a wrong parse cannot satisfy that by being wrong consistently.

One scanner tracks the three ways a line can look like an import without being
one: Lean's block comments (which nest, and which `/--` opens), line comments,
and string literals.

Run:
    python Tools/shared-imports-sync.py            # check, exits 1 on drift
    python Tools/shared-imports-sync.py --write    # rewrite the blocks
"""

import io
import re
import sys
from pathlib import Path

TARGETS = ("Tools/DeclNames.lean", "Tools/AxiomAudit.lean")
LIBRARY_ROOT = "Grass"
IMPORT_LINE = re.compile(
    r"^import[ \t]+(" + LIBRARY_ROOT + r"(?:\.[A-Za-z_][A-Za-z0-9_']*)+)[ \t]*$")
# A Lean module name is dot-separated identifiers. A file named `A.B.lean`
# would otherwise render an import of a module that cannot exist.
SEGMENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def modules_on_disk() -> list[str]:
    """Every module `lake` builds under `Grass/`, as import names."""
    root = Path(LIBRARY_ROOT)
    if not root.is_dir():
        sys.exit(
            f"no {LIBRARY_ROOT}/ directory here. This tool rewrites import "
            "lists against the tree, and run from the wrong directory it would "
            "compute a different tree; refusing.")
    parts = [path.with_suffix("").parts for path in root.rglob("*.lean")]
    if not parts:
        sys.exit(f"{LIBRARY_ROOT}/ contains no .lean files; refusing to write "
                 "an empty import list")
    # Each *path component* must be a single Lean identifier. Validating the
    # joined name instead would accept `Grass/A.B.lean`, whose dot survives
    # `with_suffix` and turns into a module separator, rendering
    # `import Grass.A.B` -- a name that parses and cannot resolve.
    bad = [".".join(p) for p in parts
           if not all(SEGMENT.match(segment) for segment in p)]
    if bad:
        sys.exit(
            f"these paths are not spellable as Lean module names: {bad}. "
            "Writing them would produce a file that does not parse; rename the "
            "files or teach this tool why they are acceptable.")
    return sorted(".".join(p) for p in parts)


def code_line_starts(text: str) -> list[int]:
    """Offsets of line starts that begin outside any comment or string."""
    starts: list[int] = []
    depth = 0
    in_line_comment = False
    in_string = False
    at_line_start = True
    index = 0
    length = len(text)
    while index < length:
        char = text[index]
        if at_line_start:
            if depth == 0 and not in_string and not in_line_comment:
                starts.append(index)
            at_line_start = False
        if char == "\n":
            in_line_comment = False
            at_line_start = True
            index += 1
            continue
        if in_line_comment:
            index += 1
            continue
        if in_string:
            if char == "\\":
                index += 2
                continue
            if char == '"':
                in_string = False
            index += 1
            continue
        pair = text[index:index + 2]
        if pair == "/-":
            depth += 1
            index += 2
            continue
        if pair == "-/" and depth > 0:
            depth -= 1
            index += 2
            continue
        if depth > 0:
            index += 1
            continue
        if pair == "--":
            in_line_comment = True
            index += 2
            continue
        if char == '"':
            in_string = True
            index += 1
            continue
        index += 1
    return starts


def import_spans(text: str) -> list[tuple[int, int, str]]:
    """(start, end, module) for each real library-import line.

    `end` is just past the line terminator, so removing a span leaves no blank
    line behind. Only lines that *begin in code* are considered.
    """
    spans = []
    for start in code_line_starts(text):
        newline = text.find("\n", start)
        end = len(text) if newline == -1 else newline + 1
        line = text[start:end].rstrip("\n").rstrip("\r")
        match = IMPORT_LINE.match(line)
        if match:
            spans.append((start, end, match.group(1)))
    return spans


def strip_imports(text: str) -> str:
    """Everything that is not a real import line, in order and byte-exact."""
    kept = []
    cursor = 0
    for start, end, _ in import_spans(text):
        kept.append(text[cursor:start])
        cursor = end
    kept.append(text[cursor:])
    return "".join(kept)


def render(text: str, wanted: list[str]) -> str:
    """Splice a sorted block in at the first import, preserving every other byte."""
    spans = import_spans(text)
    first_start, first_end, _ = spans[0]
    terminator = "\r\n" if text[first_start:first_end].endswith("\r\n") else "\n"
    block = "".join(f"import {name}{terminator}" for name in wanted)
    pieces = [text[:first_start], block]
    cursor = first_end
    for start, end, _ in spans[1:]:
        pieces.append(text[cursor:start])
        cursor = end
    pieces.append(text[cursor:])
    return "".join(pieces)


BOM = "﻿"


def process(path: str, wanted: list[str], write: bool) -> list[str]:
    whole = io.open(path, encoding="utf-8", newline="").read()
    # A byte-order mark sits *before* the first character of the first line, so
    # `^import` does not match it. Left in place, the first import is invisible
    # and gets re-added below the mark as a duplicate -- which a reviewer found
    # and `--check` then called clean. Held aside and restored verbatim, so a
    # file that had one still has one and a file that did not still does not.
    mark, raw = (BOM, whole[len(BOM):]) if whole.startswith(BOM) else ("", whole)
    found = [name for _, _, name in import_spans(raw)]

    if not found:
        sys.exit(
            f"{path} contains no `import {LIBRARY_ROOT}.` line outside a "
            "comment or string. This tool maintains that block and will not "
            "guess where to put a new one.")

    problems: list[str] = []
    for name in wanted:
        if name not in found:
            problems.append(f"{path}: missing  import {name}")
    for name in found:
        if name not in wanted:
            problems.append(
                f"{path}: stale    import {name}  (no such file in the tree)")
    for name in sorted({n for n in found if found.count(n) > 1}):
        problems.append(f"{path}: repeated import {name}")
    if not problems and found != wanted:
        problems.append(f"{path}: out of order (the block must be sorted)")

    if not (write and problems):
        return problems

    updated = render(raw, wanted)

    # Checked against the original text, not against a second run of this
    # file's own reader on its own output.
    if strip_imports(updated) != strip_imports(raw):
        raise SystemExit(
            f"{path}: refusing to write. The rewrite would have changed "
            "something other than the import lines, which means this tool "
            "mis-read the file. Nothing was changed.")
    if [n for _, _, n in import_spans(updated)] != wanted:
        raise SystemExit(
            f"{path}: refusing to write. The rewritten import block does not "
            "read back as the intended list. Nothing was changed.")

    io.open(path, "w", encoding="utf-8", newline="").write(mark + updated)
    return problems


def main(argv: list[str]) -> int:
    write = "--write" in argv[1:]
    unknown = [a for a in argv[1:] if a != "--write"]
    if unknown:
        sys.exit(f"unknown argument(s): {unknown}. Use --write or no argument.")

    wanted = modules_on_disk()
    problems: list[str] = []
    for path in TARGETS:
        if not Path(path).is_file():
            sys.exit(f"{path} is missing; this tool maintains it and will not "
                     "silently skip it")
        problems.extend(process(path, wanted, write))

    if not problems:
        print(f"shared import lists: both registries import all "
              f"{len(wanted)} modules under {LIBRARY_ROOT}/, in order")
        return 0

    if write:
        print(f"shared import lists: rewrote {len(TARGETS)} registries to "
              f"{len(wanted)} modules. Changes:")
    else:
        print("shared import lists are out of step with the tree:\n")
    sys.stdout.flush()
    for problem in problems:
        # A mis-parsed line can carry anything and a Windows console is cp1252
        # by default; a diagnosis must not die on its own output.
        sys.stdout.buffer.write(("  " + problem).encode("utf-8", "replace")
                                + b"\n")
    sys.stdout.buffer.flush()
    if write:
        return 0
    print(
        "\nRun `python Tools/shared-imports-sync.py --write` in the same commit "
        "as the module change. The import must land with the module it names: "
        "`lake env lean` resolves these against the current tree, so an import "
        "of a module that is not there yet fails for every agent, not just the "
        "one that added it.")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
