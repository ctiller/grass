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

## Only the header is read, and that is the whole design

Four versions of this tool corrupted files while `--check` reported success, and
each fix addressed the shape that had just been demonstrated rather than the
reason the shapes kept arriving. The reason was scope: the tool read the *whole
file* looking for lines that looked like imports, so every construct Lean allows
anywhere -- comments, nested comments, doc comments, line comments mentioning
`/-`, string literals containing `import`, `Char` literals like `'"'`, raw
strings ending in a backslash -- was a chance to mistake data for code. The last
version tracked comments and strings and still lost, because `'"'` desynchronised
its string state and the block was written inside a string literal.

Lean requires every `import` to precede every command. So the imports live in a
*header*: a prefix made only of whitespace, comments, and import lines. A string
literal cannot appear there, because there is no term there to contain one.
Restricting the scan to that prefix removes the entire class rather than the
last instance of it: `parse_header` stops at the first thing that is not one of
those three, and nothing after that point is examined or touched.

## The invariant is checked without this file's own reader

The previous version asserted that "everything which is not an import line
survives", using its own parser on both sides. That is not an invariant, it is a
consistency check, and a reviewer satisfied it three times with a wrong parse.
The check now uses facts that do not depend on the scanner at all: the text
before the first import must be unchanged, the text from the end of the last
import onward must be unchanged, and the region between them must consist only
of import lines and the material that already sat between them.

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
# A trailing line comment on an import is legal Lean and was invisible to an
# anchored `$`, so the tool duplicated the import beneath itself.
IMPORT_LINE = re.compile(
    r"^import[ \t]+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
    r"[ \t]*(?:--[^\n]*)?$")
SEGMENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
BOM = "﻿"


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
    # joined name would accept `Grass/A.B.lean`, whose dot survives
    # `with_suffix` and becomes a module separator.
    bad = [".".join(p) for p in parts
           if not all(SEGMENT.match(segment) for segment in p)]
    if bad:
        sys.exit(
            f"these paths are not spellable as Lean module names: {bad}. "
            "Writing them would produce a file that does not parse; rename the "
            "files or teach this tool why they are acceptable.")
    return sorted(".".join(p) for p in parts)


def parse_header(text: str) -> tuple[list[tuple[int, int, str]], int]:
    """Import spans in the header, and where the header ends.

    The header is the prefix of the file made of whitespace, comments and
    import lines -- everything Lean allows before the first command. Parsing
    stops at the first byte that is none of those, and an unterminated comment
    stops it too, so a malformed file is refused rather than guessed at.
    """
    spans: list[tuple[int, int, str]] = []
    index = 0
    length = len(text)
    while index < length:
        char = text[index]
        if char in " \t\r\n":
            index += 1
            continue
        pair = text[index:index + 2]
        if pair == "--":
            newline = text.find("\n", index)
            if newline == -1:
                return spans, length
            index = newline + 1
            continue
        if pair == "/-":
            depth = 0
            scan = index
            while scan < length - 1:
                window = text[scan:scan + 2]
                if window == "/-":
                    depth += 1
                    scan += 2
                    continue
                if window == "-/":
                    depth -= 1
                    scan += 2
                    if depth == 0:
                        break
                    continue
                scan += 1
            else:
                # Unterminated: the header cannot be delimited, so stop here
                # and let the caller refuse rather than write into a comment.
                return spans, index
            if depth != 0:
                return spans, index
            index = scan
            continue
        newline = text.find("\n", index)
        end = length if newline == -1 else newline + 1
        line = text[index:end].rstrip("\n").rstrip("\r")
        match = IMPORT_LINE.match(line)
        if not match:
            return spans, index
        if match.group(1).split(".")[0] == LIBRARY_ROOT:
            spans.append((index, end, match.group(1)))
        index = end
    return spans, length


def render(text: str, spans, wanted: list[str]) -> str:
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


def verify(before: str, after: str, spans, wanted: list[str]) -> str | None:
    """Reasons the rewrite is unsafe, computed without this file's parser.

    Nothing here calls `parse_header`. The prefix before the first import and
    the suffix from the end of the last import are compared as strings, and the
    middle is required to contain only import lines plus whatever already sat
    between the originals.
    """
    prefix = before[:spans[0][0]]
    suffix = before[spans[-1][1]:]
    if not after.startswith(prefix):
        return "the text before the first import changed"
    if not after.endswith(suffix):
        return "the text after the last import changed"
    middle = after[len(prefix):len(after) - len(suffix)] if suffix else \
        after[len(prefix):]
    between = "".join(
        before[a[1]:b[0]] for a, b in zip(spans, spans[1:]))
    residue = middle
    for name in wanted:
        line = f"import {name}"
        position = residue.find(line)
        if position == -1:
            return f"the rewritten block does not contain {line}"
        residue = residue[:position] + residue[position + len(line):]
    if residue.strip("\r\n \t") != between.strip("\r\n \t"):
        return ("the material between the imports changed: "
                f"{between!r} became {residue!r}")
    return None


def process(path: str, wanted: list[str], write: bool) -> list[str]:
    whole = io.open(path, encoding="utf-8", newline="").read()
    mark, raw = (BOM, whole[len(BOM):]) if whole.startswith(BOM) else ("", whole)
    spans, header_end = parse_header(raw)
    found = [name for _, _, name in spans]

    if not found:
        sys.exit(
            f"{path} has no `import {LIBRARY_ROOT}.` line in its header. This "
            "tool maintains that block and will not guess where to put a new "
            "one.")

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

    updated = render(raw, spans, wanted)
    reason = verify(raw, updated, spans, wanted)
    if reason is not None:
        raise SystemExit(
            f"{path}: refusing to write -- {reason}. Nothing was changed.")

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
