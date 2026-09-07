"""Keep the shared audit registries' import lists equal to the tree.

`Tools/DeclNames.lean` and `Tools/AxiomAudit.lean` each have to import every
module in the build: a name the declaration list cannot see is a name
`Tools/DocstringAudit.py` reports as invented, and a module the axiom audit
cannot see is a module whose axioms nobody counted. Both lists were maintained
by hand, and that had two costs that showed up within a day of each other.

The first is drift. When this tool was written `Tools/AxiomAudit.lean` was
three modules behind the tree, and therefore behind `Tools/DeclNames.lean` too.

The second is worse, and is why this exists rather than a reminder in a header.
Those two files sit in one agent's exclusive scope, so an agent adding a module
anywhere else in `Grass/` could not add the line that keeps the gates honest.
Five separate requests (`g-construct:7`, `:10`, `:15`, `:17`, `:19`) queued up
behind a single owner, each one naming modules that the owner could not merge
anyway: the import must land in the same commit as the module it names, because
`lake env lean` resolves imports against the current tree and an import of a
module that is not there yet fails outright for everyone. `c-stdlib:25` reports
hitting exactly that.

So the route is mechanical rather than social. Any agent adding a module runs
this with `--write` in the same commit, and the resulting diff is confined to a
sorted import block. `--check` is the gate, and it fails loudly with the exact
lines to add or drop.

Sorted rather than grouped, because a sorted list is what two agents adding
modules concurrently can both produce without a conflict that has to be
resolved by taste.

Run:
    python Tools/shared-imports-sync.py            # check, exits 1 on drift
    python Tools/shared-imports-sync.py --write    # rewrite the blocks
"""

import io
import sys
from pathlib import Path

TARGETS = ("Tools/DeclNames.lean", "Tools/AxiomAudit.lean")
LIBRARY_ROOT = "Grass"


def modules_on_disk() -> list[str]:
    """Every module `lake` builds under `Grass/`, as import names."""
    root = Path(LIBRARY_ROOT)
    if not root.is_dir():
        sys.exit(
            f"no {LIBRARY_ROOT}/ directory here. This tool rewrites import "
            "lists against the tree, and run from the wrong directory it would "
            "compute an empty tree and delete every import; refusing.")
    names = sorted(
        ".".join(path.with_suffix("").parts)
        for path in root.rglob("*.lean")
    )
    if not names:
        sys.exit(f"{LIBRARY_ROOT}/ contains no .lean files; refusing to write "
                 "an empty import list")
    return names


def split_block(text: str, newline: str) -> tuple[list[str], list[str], str]:
    """Return (leading non-library imports, current library imports, rest)."""
    lines = text.split(newline)
    other: list[str] = []
    current: list[str] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        if line.startswith(f"import {LIBRARY_ROOT}."):
            current.append(line[len("import "):])
        elif line.startswith("import "):
            other.append(line)
        elif line.strip() == "" and current == [] and index < len(lines) - 1:
            # Blank lines before the block start are kept with the header.
            other.append(line)
        else:
            break
        index += 1
    return other, current, newline.join(lines[index:])


def process(path: str, wanted: list[str], write: bool) -> list[str]:
    raw = io.open(path, encoding="utf-8", newline="").read()
    newline = "\r\n" if "\r\n" in raw else "\n"
    other, current, rest = split_block(raw, newline)

    missing = [name for name in wanted if name not in current]
    extra = [name for name in current if name not in wanted]
    duplicated = sorted({name for name in current if current.count(name) > 1})

    problems = []
    for name in missing:
        problems.append(f"{path}: missing  import {name}")
    for name in extra:
        problems.append(
            f"{path}: stale    import {name}  (no such file in the tree)")
    for name in duplicated:
        problems.append(f"{path}: repeated import {name}")

    if write and (missing or extra or duplicated):
        block = newline.join(f"import {name}" for name in wanted)
        io.open(path, "w", encoding="utf-8", newline="").write(
            newline.join(other) + newline + block + newline + rest)
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
              f"{len(wanted)} modules under {LIBRARY_ROOT}/")
        return 0

    if write:
        print(f"shared import lists: rewrote {len(TARGETS)} registries to "
              f"{len(wanted)} modules. Changes:")
        for problem in problems:
            print("  " + problem)
        return 0

    print("shared import lists are out of step with the tree:\n")
    for problem in problems:
        print("  " + problem)
    print(
        "\nRun `python Tools/shared-imports-sync.py --write` in the same commit "
        "as the module change. The import must land with the module it names: "
        "`lake env lean` resolves these against the current tree, so an import "
        "of a module that is not there yet fails for every agent, not just the "
        "one that added it.")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
