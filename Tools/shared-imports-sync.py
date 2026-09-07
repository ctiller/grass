"""Keep the shared audit registries' import lists equal to the tree.

`Tools/DeclNames.lean` and `Tools/AxiomAudit.lean` each have to import every
module in the build: a name the declaration list cannot see is a name
`Tools/DocstringAudit.py` reports as invented, and a module the axiom audit
cannot see is a module whose axioms nobody counted. Both lists were maintained
by hand, and that had two costs.

The first is drift. When this tool was written `Tools/AxiomAudit.lean` was three
modules behind the tree, and therefore behind `Tools/DeclNames.lean` too.

The second is worse. Those two files sit in one agent's exclusive scope, so an
agent adding a module anywhere else in `Grass/` could not add the line that
keeps the gates honest. Five requests (`g-construct:7`, `:10`, `:15`, `:17`,
`:19`) queued behind one owner, each naming modules that owner could not merge
anyway: the import must land in the same commit as the module it names, because
`lake env lean` resolves imports against the current tree and an import of a
module that is not there yet fails outright for everyone. `c-stdlib:25` reports
hitting exactly that.

So the route is mechanical. Any agent adding a module runs this with `--write`
in the same commit, and the diff is a sorted import block.

## Why this rewrites so defensively

The first version parsed the import block as "the leading run of lines that look
like imports", stopping at the first line that did not, and then re-emitted that
run. Cold reviewers broke it in five file shapes across two sessions, and every
one of them ended with `--check` reporting success.

Two destroyed content outright:

* one CRLF line in an otherwise-LF file made the whole remainder of the file
  parse as a single import line, so `--write` deleted every declaration in
  `Tools/AxiomAudit.lean` and left an import list behind;
* a Lean block comment containing an example `import Grass.X` line, placed
  before the real imports, fixed the insertion point inside the comment, so
  `--write` moved every import into it and the registry then imported nothing.
  That shape was found sitting in `Tools/DeclNames.lean` in the working tree,
  not invented for the test.

Three produced a wrong import block rather than destroying anything:

* one blank line inside the block hid the imports after it, which `--write` then
  re-added, producing 53 duplicates that `--check` could not see;
* a line comment inside the block did the same;
* a module docstring above the imports made the block start at line 0, so the
  new list was written before the docstring and the old one left after it.

The lesson is that a rewriter must not be trusted to have parsed correctly, and
that an invariant checked with the parser under test is not an invariant: the
block-comment shape passed the re-parse fixpoint precisely because both sides
of it agreed on the same wrong reading. So:

* lines are split with `splitlines`, which treats CRLF, LF and a mixture alike;
* `import Grass.` lines are collected from anywhere in the file rather than from
  a leading run, so a blank line or a comment cannot hide any;
* **every other line is carried through untouched**, and that is asserted rather
  than assumed -- `plan` returns the surviving lines and `process` checks they
  are exactly the file's non-library-import lines, in order;
* after writing, the result is re-parsed and must be a fixpoint with the same
  non-import content. A failure raises before anything else is written.

Sorted rather than grouped, because a sorted list is what two agents adding
modules concurrently can both produce without a conflict resolved by taste.
Order is compared, not just membership, so an unsorted list is drift.

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
LIBRARY_IMPORT = re.compile(r"^import\s+(" + LIBRARY_ROOT + r"\.[A-Za-z0-9_.']*)\s*$")
# Lean identifiers, so a stray file name cannot become a broken import line.
MODULE_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$")


def modules_on_disk() -> list[str]:
    """Every module `lake` builds under `Grass/`, as import names."""
    root = Path(LIBRARY_ROOT)
    if not root.is_dir():
        sys.exit(
            f"no {LIBRARY_ROOT}/ directory here. This tool rewrites import "
            "lists against the tree, and run from the wrong directory it would "
            "compute a different tree; refusing.")
    names = sorted(
        ".".join(path.with_suffix("").parts)
        for path in root.rglob("*.lean")
    )
    if not names:
        sys.exit(f"{LIBRARY_ROOT}/ contains no .lean files; refusing to write "
                 "an empty import list")
    bad = [name for name in names if not MODULE_NAME.match(name)]
    if bad:
        sys.exit(
            f"these paths are not spellable as Lean module names: {bad}. "
            "Writing them would produce a file that does not parse; rename the "
            "files or teach this tool why they are acceptable.")
    return names


def comment_depth_after(line: str, depth: int) -> int:
    """Block-comment nesting depth at the end of `line`, starting from `depth`.

    Lean block comments nest, and `/--` opens one as surely as `/-` does.
    """
    index = 0
    while index < len(line) - 1:
        pair = line[index:index + 2]
        if pair == "/-":
            depth += 1
            index += 2
            continue
        if pair == "-/" and depth > 0:
            depth -= 1
            index += 2
            continue
        index += 1
    return depth


def plan(text: str) -> tuple[list[str], list[str], int]:
    """Return (library imports found, all other lines, where the block starts).

    Library imports are collected from anywhere in *code*: a blank line, a line
    comment or a stray carriage return must not be able to hide one.

    Lines inside a block comment are not code, and that distinction is the whole
    of this function's difficulty. A reviewer put an ordinary explanatory
    comment in a registry --

        /- To add a module by hand write, e.g.
        import Grass.Memory.Access
        -/

    -- and the earlier version read that example as a real import. Worse, when
    the comment came before the real imports it fixed the insertion point inside
    the comment, so `--write` moved every import into it: the file then imported
    nothing, and `--check` reported it clean, because both sides of the fixpoint
    check used this same reader. An invariant asserted with the parser under
    test cannot catch the parser being wrong, so the parser has to be right.

    That shape was not hypothetical; it was sitting in `Tools/DeclNames.lean`
    in the working tree when the reviewer found it.
    """
    lines = text.splitlines()
    found: list[str] = []
    others: list[str] = []
    first: int | None = None
    depth = 0
    for line in lines:
        opened_before = depth
        depth = comment_depth_after(line, depth)
        match = LIBRARY_IMPORT.match(line) if opened_before == 0 else None
        if match:
            if first is None:
                first = len(others)
            found.append(match.group(1))
        else:
            others.append(line)
    return found, others, 0 if first is None else first


def render(wanted: list[str], others: list[str], at: int, newline: str) -> str:
    block = [f"import {name}" for name in wanted]
    return newline.join(others[:at] + block + others[at:]) + newline


def process(path: str, wanted: list[str], write: bool) -> list[str]:
    raw = io.open(path, encoding="utf-8", newline="").read()
    newline = "\r\n" if raw.count("\r\n") * 2 >= raw.count("\n") else "\n"
    found, others, at = plan(raw)

    if not found:
        sys.exit(
            f"{path} contains no `import {LIBRARY_ROOT}.` line. This tool "
            "maintains that block and will not guess where to put a new one.")

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

    updated = render(wanted, others, at, newline)

    # Nothing but the import block may move. Re-parse the rendered text and
    # require a fixpoint with identical surviving lines before touching disk.
    again, others_again, at_again = plan(updated)
    if again != wanted or others_again != others or at_again != at:
        raise SystemExit(
            f"{path}: refusing to write. Re-parsing the rewritten file did not "
            "reproduce it, which means this tool mis-read the original. "
            "Nothing was changed. Report this with the file attached.")

    io.open(path, "w", encoding="utf-8", newline="").write(updated)
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

    lines = ["  " + problem for problem in problems]
    if write:
        print(f"shared import lists: rewrote {len(TARGETS)} registries to "
              f"{len(wanted)} modules. Changes:")
    else:
        print("shared import lists are out of step with the tree:\n")
    for line in lines:
        # Windows consoles are cp1252 by default and a mis-parsed line can
        # carry anything; a diagnosis must not die on its own output.
        sys.stdout.buffer.write(line.encode("utf-8", "replace") + b"\n")
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
