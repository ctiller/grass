#!/usr/bin/env python3
"""Report fixture definitions nothing uses.

A `def` under `Tests/` exists to be consumed by a theorem. One that nothing mentions
is a state someone built for a claim that has since changed, and it reads as coverage
while proving nothing — the same defect class as a field nothing projects
(`Tools/ConsultedAudit.py`) and a constructor nothing builds
(`Tools/ReachabilityAudit.py`), in the one place those two do not look.

It is not hypothetical. `Tests/Memory/Loans.lean` carried `lentThenReused`, a state
built by reallocating under an outstanding loan, from before that reallocation was
refused: after the refusal landed the definition still elaborated, still looked like a
fixture, and its `.getD` silently returned the *unreallocated* state. Nothing used it,
so nothing failed. `currentProv` was the same story from the same commit.

**What this checks, exactly.** For every `def` declared under `Tests/`, within `SCOPE`,, it counts
occurrences of that name in the comment- and string-stripped sources of `Grass/`,
`Tests/` and `Tools/`. One occurrence is the declaration itself; zero further ones is
a report.

**What it does not check**, stated because every tool in this directory has been
corrected for advertising a stronger reading:

- **It covers this branch's tree, not the repository.** `SCOPE` below names the
  subtrees, which are the ones this branch had before merging `origin/main`:
  `Grass/{Certificate,Core,Memory,Obligation,Op,Resource,Semantics,Std,Trust,
  Verify}` and `Tests/{Foundation,Memory,Op,Resource,Std}`. `Grass/ISA`,
  `Grass/ABI`, `Grass/Process` and their fixtures are **not covered by this gate
  or by anything of this kind** — not because they are clean, but because
  reporting a declaration as unread is a judgement only that code's owner can
  make. Four of the subtrees that *are* covered belong to other owners too; their
  findings are allowlisted with the reason and reported rather than decided here.

  The comment above `SCOPE` used to say "the honest statement of coverage is in
  the module docstring", and there was no such statement in any of the four
  docstrings. A sentence that delegates to text nobody wrote is worse than no
  sentence: it reads as a promise kept.

- Comments are stripped, so a fixture named only in prose counts as unused. That is
  deliberate: a docstring citing a state nothing tests is exactly what this is for.
  `Tools/CitationAudit.py` is what keeps such prose from naming something that does
  not exist at all.
- It is lexical and namespace-blind. A `def` in one test module and a `def` of the
  same name in another are one name here, so using either satisfies both.
- "Used" means "mentioned", not "meaningfully consumed". A fixture mentioned once, in
  a theorem that proves something vacuous about it, passes. The vacuity of the
  *theorem* is not something a regex can see.
- A definition consumed by an *environment-walking* tool rather than by name is
  invisible: `Tools/AxiomAudit.lean` discovers `VerifiedProgram` producers from their
  types, so a fixture that exists to be discovered has no textual consumer. Both such
  definitions in the tree are in `ALLOWED` with that reason.
- It does not look at `theorem` or `abbrev` declarations. An unused theorem is not
  the same defect — a law nothing cites is still a law — and `abbrev`s in `Tests/`
  are type aliases.

`--self-test` seeds each class this file claims to catch and each near-miss it must
stay quiet on. Run it after changing the scanner.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# **Scope: the tree this branch had before merging main.**
#
# Merging `origin/main` put three other owners' trees under these globs -- `Grass/ISA`,
# `Grass/ABI`, `Grass/Process` and their fixtures -- and this gate immediately reported
# findings in them. Every one may be true and none is this branch's to judge: an
# allowlist entry here records that *somebody read the corpus and decided*, and nobody
# on this branch has read theirs.
#
# **The first version of this list was written by hand and was wrong in both
# directions.** It named eight subtrees from memory and dropped three that were in this
# branch's own tree before the merge -- `Grass/Certificate.lean`, `Grass/Verify/` and
# `Tests/Foundation.lean` -- which cost one live finding and made two allowlist entries
# read as inert. A scope written from what the author remembered owning is the same
# defect as a count written from reading rather than running. It is the pre-merge tree
# now, which is a fact rather than a recollection: `git ls-tree b9d4200 Grass/ Tests/`.
#
# Widening it is one edit, and the module docstring says what is not covered.
SCOPE = ("Certificate", "Core", "Memory", "Obligation", "Op", "Resource", "Semantics",
         "Std", "Trust", "Verify", "Foundation")


def in_scope(path) -> bool:
    """Whether a path lies in one of `SCOPE`'s subtrees.

    Relative to `ROOT`, not by scanning absolute components for the first `Grass` or
    `Tests`. The scanning form had two failures review demonstrated: a path under a
    top-level directory this branch has not created yet fell out silently, and a
    checkout directory *named* `Grass` -- which is what this project is called -- made
    the repository root the first match and put every file out of scope.
    """
    try:
        parts = path.resolve().relative_to(ROOT).parts
    except ValueError:
        # Outside the repository: not this gate's business, and not silently in scope.
        return False
    if len(parts) < 2 or parts[0] not in ("Grass", "Tests"):
        return True
    return parts[1].removesuffix(".lean") in SCOPE


def scope_is_covered(paths, trees=("Grass", "Tests")) -> list[str]:
    """Report if the scope filter has emptied the file list or lost a known subtree.

    **`SCOPE` was a coverage claim with nothing behind it.** Review dropped one token
    from it and three gates went silent for this layer while printing their success
    lines; no self-test touched `in_scope`, because every self-test writes probe files
    into a temporary directory and calls the scanner directly, so the path filter is
    never on the tested path. Only total emptiness was guarded, and only in three of the
    six gates.

    A floor rather than an emptiness check, in the shape
    `Tools/DocstringAudit.py`'s `declaration_names` already uses (`if len(known) <
    1000`): every subtree named in `SCOPE` that exists on disk must contribute at
    least one file.

    **What this cannot catch, stated because the first version of this paragraph
    claimed it could.** It derives its expectation from `SCOPE`, so deleting a token
    from `SCOPE` deletes the check for that subtree along with it -- exactly the
    attack it was written against, and it passes. What it does catch is the globs or
    `in_scope` breaking under a `SCOPE` that still names the subtree, which is the
    other half and the one no gate had.

    The authority on `SCOPE`'s *contents* is `self_test`, which asserts membership
    against four hard-coded paths rather than against `SCOPE`. CI runs every gate's
    self-test before the gate, so a narrowed `SCOPE` fails there. A check derived
    from the thing it is checking is not a check, and saying which half is which is
    the whole content of this paragraph.

    `trees` is which of `Grass/` and `Tests/` this gate's list actually covers;
    asking about the other one reports every subtree of it as unreached, which
    is the first thing this check did.
    """
    missing = []
    for name in SCOPE:
        for tree in trees:
            candidate = ROOT / tree / name
            if not (candidate.is_dir() or candidate.with_suffix(".lean").is_file()):
                continue
            prefix = (tree, name)
            if not any(
                    p.resolve().relative_to(ROOT).parts[:2] in
                    (prefix, (tree, name + ".lean"))
                    for p in paths):
                missing.append(f"  {tree}/{name}: in SCOPE, on disk, and no file "
                               "reached the scan")
    return missing


DECLARED_IN = [p for p in sorted((ROOT / "Tests").rglob("*.lean")) if in_scope(p)]
USED_IN = (DECLARED_IN + sorted((ROOT / "Grass").rglob("*.lean"))
           + sorted((ROOT / "Tools").rglob("*.lean")))

# Lean identifiers here use subscript digits and primes as well as ASCII.
IDENT = r"[A-Za-z_][A-Za-z0-9_'₀-₉¹²³]*"
# `^[ \t]*`, not `^`. `BLOCK.sub(blank, ...)` leaves what followed a same-line
# docstring where it was, so `/-- doc -/ def orphan := 1` becomes an *indented* `def`
# -- and this pattern anchored hard at column zero, so review seeded a fixture written
# that way and the gate stayed green.
DEFINITION = re.compile(
    r"^[ \t]*(?:private\s+|protected\s+)?def\s+(" + IDENT + r")", re.MULTILINE)
def blank(match: "re.Match[str]") -> str:
    """Replace a match with as many newlines as it spanned, keeping line numbers."""
    return chr(10) * match.group(0).count(chr(10))

# Comments and string literals, blanked so line numbers survive.
#
# **These three patterns and this order are the same in every gate in this
# directory, and were not.** Review found `SourceLocationAudit.py` blanking real code
# because a `/-` inside a string literal opened a comment; that was repaired there and
# the four siblings kept the defect, mirrored -- they ran `STRING` before `LINE`, so a
# `" in a *line comment* opened a string and everything down to the next quote was
# erased. Review appended a real door call between two such comments and every gate
# stayed green.
#
# The order is `STRING`, then `BLOCK`, then `LINE`, and `STRING` cannot span lines.
# That is the only arrangement where neither construct can swallow the other: a quote
# inside a comment reaches the end of its own line and no further, and that line is a
# comment the next two patterns blank anyway. `blank` rather than deletion, because a
# report that points at the wrong line is the defect this file's sibling was found
# with twice.

# Fixtures deliberately carried without a user, each with its reason. The two entries
# this tool was written against -- `currentProv` and `lentThenReused` in
# `Tests/Memory/Loans.lean` -- were deleted rather than listed.
ALLOWED: set[str] = {
    # Consumed by an environment-walking audit rather than by name.
    # `#audit_verified_programs`, which `Tests/Foundation.lean` runs at the end of the
    # file the fixtures live in and which `audit-trust.ps1` re-runs, discovers
    # `VerifiedProgram` producers from their *types* and names both of these in its
    # output -- so no source mentions them and this tool cannot see the consumer.
    #
    # This comment said `Tools/AxiomAudit.lean` did that, and review checked: it
    # imports `Grass.*` only, walks `Grass/` on disk, and prints one summary line
    # naming no declaration. It cannot see either fixture. The exemptions are right
    # and the pointer a reviewer would follow to verify them was not. They belong to another owner's module and the shape is deliberate:
    # `aliasedVerified` exists to be found through an alias and `inferredVerified`
    # through an inferred type.
    "aliasedVerified",
    "inferredVerified",
    # Carried deliberately, and its own docstring says so: it is one of a pair of
    # definitions in `Tests/Std/SpikeSurface.lean` showing how a spike line "has to be
    # written as today", present "so that the gap is visible in compiled code rather
    # than only in a plan". Elaborating *is* its purpose, so there is nothing for a
    # consumer to check; the `resultMove` beside it has an `example` because there is.
    # Another owner's module, arrived by merging main.
    "deviceExtensionNames",
}


# **A scanner rather than three regexes, because Lean nests block comments and a
# regex cannot.** What stood here was `/-.*?-/` non-greedy, `--.*?$`, and a
# single-line string, applied in an order two rounds argued about. Both remaining
# orders were wrong, and review demonstrated both:
#
#   * `/- outer /- inner -/ code -/` -- the non-greedy block closes at the first
#     `-/`, so `code` survives as source. A declaration referenced only inside a
#     comment counted as used, and a fixture nothing consumes went unreported.
#   * `-- a note mentioning /- something` -- `LINE` ran last, so a `/-` inside a
#     line comment opened a block for `BLOCK`, which swallowed every line down to
#     the next `-/` anywhere in the file. Review hid a real `MemoryState.alias`
#     call in `Grass/Memory/Loan.lean` behind one and all nine gates stayed green
#     -- the same demonstration that put `alias` in `DOORS`, reached through the
#     stripper instead of through the allowlist.
#
# The scanner tracks block-comment depth, opens a line comment on `--` only at
# depth zero and outside a string, and keeps a string literal from spanning lines.
# Every consumed character becomes a space and every newline is kept, so offsets
# and line numbers are the source's. Five gates share this; it is written out in
# each rather than imported, which is the same duplication the three patterns had.
#
# `QUOTE` and `BACKSLASH` are spelled with `chr` so that this file's own source
# carries neither where a reader might take it for the thing being matched.
QUOTE = chr(34)
BACKSLASH = chr(92)


def strip(source: str) -> str:
    """Remove block comments, line comments and string literals."""
    out: list[str] = []
    depth = 0
    in_string = False
    in_line_comment = False
    index = 0
    size = len(source)
    while index < size:
        char = source[index]
        if char == chr(10):
            out.append(chr(10))
            in_line_comment = False
            # A string literal does not span lines in Lean, so one left open at a
            # newline is a lexical error in the source rather than licence to
            # blank the rest of the file.
            in_string = False
            index += 1
            continue
        if in_line_comment:
            out.append(chr(32))
            index += 1
            continue
        if in_string:
            if char == BACKSLASH and index + 1 < size:
                out.append(chr(32) * 2)
                index += 2
                continue
            out.append(chr(32))
            if char == QUOTE:
                in_string = False
            index += 1
            continue
        if depth > 0:
            if source.startswith(chr(47) + chr(45), index):
                depth += 1
                out.append(chr(32) * 2)
                index += 2
                continue
            if source.startswith(chr(45) + chr(47), index):
                depth -= 1
                out.append(chr(32) * 2)
                index += 2
                continue
            out.append(chr(32))
            index += 1
            continue
        if source.startswith(chr(47) + chr(45), index):
            depth = 1
            out.append(chr(32) * 2)
            index += 2
            continue
        if source.startswith(chr(45) * 2, index):
            in_line_comment = True
            out.append(chr(32) * 2)
            index += 2
            continue
        if char == QUOTE:
            in_string = True
            out.append(chr(32))
            index += 1
            continue
        out.append(char)
        index += 1
    return "".join(out)


def analyse(declared: dict[str, str], used: dict[str, str] | None = None) -> list[str]:
    """Report every `Tests/` definition mentioned nowhere but its own declaration."""
    if used is None:
        used = declared
    code = {name: strip(text) for name, text in used.items()}
    reported = []
    for name in sorted(declared):
        text = strip(declared[name])
        for number, line in enumerate(text.splitlines(), start=1):
            match = DEFINITION.match(line)
            if not match:
                continue
            fixture = match.group(1)
            if fixture in ALLOWED:
                continue
            pattern = re.compile(
                r"(?<![A-Za-z0-9_'₀-₉])" + re.escape(fixture)
                + r"(?![A-Za-z0-9_'₀-₉])"
            )
            uses = sum(len(pattern.findall(body)) for body in code.values())
            if uses <= 1:
                reported.append(f"  {name}:{number}: {fixture} is defined and nothing uses it")
    return reported


def inert_entries(declared: dict[str, str],
                  used: dict[str, str] | None = None) -> list[str]:
    """The `ALLOWED` entries whose removal would change nothing.

    A leave-one-out, the shape `ConsultedAudit.py` established. This gate had no such
    check while four siblings grew one -- three of them after review found dead entries,
    and the fourth after review found its check reporting every entry it had. An
    allowlist is a record of decisions, so an entry that suppresses nothing records a
    decision about nothing; here that is the *good* case, because an entry becomes inert
    exactly when somebody starts using the fixture.

    Reported rather than failed, for that reason.
    """
    global ALLOWED
    original = set(ALLOWED)
    base = set(analyse(declared, used))
    inert = []
    for entry in sorted(original):
        ALLOWED = original - {entry}
        if not set(analyse(declared, used)) - base:
            inert.append(entry)
    ALLOWED = original
    return inert


def self_test() -> int:
    failures = 0

    # Review's two shapes. A same-line docstring left the `def` indented and the
    # pattern anchored at column zero; and `BLOCK.sub("", ...)` deleted the newlines
    # of every docstring above a fixture, so no line number this gate printed was ever
    # right -- the defect `DoorAudit.py` records finding and repairing in itself.
    inline_doc = {"Tests/Memory/Loans.lean": "/-- doc -/ def orphan : Nat := 1\n"}
    if not analyse(inline_doc):
        print("  SELF-TEST FAILED: a fixture sharing a line with its docstring is not "
              "reported")
        failures += 1
    numbered = {"Tests/Memory/Loans.lean":
                "/-\nthree\nline\n-/\ndef orphan : Nat := 1\n"}
    reports = analyse(numbered)
    if not reports or ":5:" not in reports[0]:
        print("  SELF-TEST FAILED: the reported line number does not survive a block "
              f"comment above the fixture: {reports}")
        failures += 1

    # A name that appears only inside a *nested* block comment is not a use. The
    # old non-greedy `/-.*?-/` closed at the first `-/`, so the text after it read
    # as source and a fixture nothing consumes went unreported.
    commented = {"Tests/Memory/Loans.lean": "def orphan : Nat := 1" + chr(10),
                 "Tests/Memory/Other.lean":
                     "/- note /- aside -/ example : Nat := orphan -/" + chr(10)}
    if not analyse(commented):
        print("  SELF-TEST FAILED: a name used only inside a nested block comment "
              "counts as a use")
        failures += 1

    dead = {"Tests/Memory/Loans.lean": "def orphan : Nat := 1\n"}
    if not analyse(dead):
        print("  SELF-TEST FAILED: a fixture nothing uses is not reported")
        failures += 1

    used = {"Tests/Memory/Loans.lean": "def kept : Nat := 1\ntheorem t : kept = 1 := rfl\n"}
    if analyse(used):
        print("  SELF-TEST FAILED: a fixture a theorem uses is reported")
        failures += 1

    elsewhere = {"Tests/Memory/Loans.lean": "def kept : Nat := 1\n"}
    consumer = dict(elsewhere)
    consumer["Grass/Memory/State.lean"] = "theorem t : kept = 1 := rfl\n"
    if analyse(elsewhere, consumer):
        print("  SELF-TEST FAILED: a fixture used from another tree is reported")
        failures += 1

    prose = {"Tests/Memory/Loans.lean":
             "def orphan : Nat := 1\n/-- `orphan` is the state. -/\ntheorem t : True := trivial\n"}
    if not analyse(prose):
        print("  SELF-TEST FAILED: a fixture named only in a comment is not reported; "
              "the module docstring says prose does not count as use")
        failures += 1

    prefix = {"Tests/Memory/Loans.lean":
              "def lent : Nat := 1\ntheorem t : lentHead = lentHead := rfl\ndef lentHead : Nat := 2\n"}
    if not analyse(prefix):
        print("  SELF-TEST FAILED: a longer name containing the fixture's name counts "
              "as a use; the boundary check is wrong")
        failures += 1

    subscripted = {"Tests/Memory/Loans.lean":
                   "def state₀ : Nat := 1\ntheorem t : state₀ = 1 := rfl\n"}
    if analyse(subscripted):
        print("  SELF-TEST FAILED: a subscripted name's use is not recognised")
        failures += 1

    theorems = {"Tests/Memory/Loans.lean": "theorem unusedLaw : True := trivial\n"}
    if analyse(theorems):
        print("  SELF-TEST FAILED [documented scope]: theorems are reported; the "
              "module docstring says only `def`s are")
        failures += 1

    # The `--inert` sweep, both directions. Four sibling gates grew this check only
    # after review found something wrong with their allowlists; this file had none at
    # all, which is why review found it by counting the gates rather than by reading
    # one.
    global ALLOWED
    saved_allowed = set(ALLOWED)
    live = {"Tests/Memory/Loans.lean": "def orphan : Nat := 1" + chr(10)}
    ALLOWED = {"orphan"}
    if inert_entries(live) != []:
        print("  SELF-TEST FAILED: an entry that suppresses a real report is called "
              "inert")
        failures += 1
    ALLOWED = {"orphan", "nothingNamedThis"}
    if inert_entries(live) != ["nothingNamedThis"]:
        print("  SELF-TEST FAILED: an entry that suppresses nothing is not reported, "
              "or a live one is")
        failures += 1
    ALLOWED = saved_allowed

    # `in_scope`, both directions, and the floor. `SCOPE` was a coverage claim with
    # nothing behind it: review dropped one token and this gate went silent for the
    # memory layer while still printing its success line. No self-test reached the
    # path filter, because every case here writes probes into a temporary directory
    # and calls the scanner directly.
    if not in_scope(ROOT / "Grass" / "Memory" / "State.lean"):
        print("  SELF-TEST FAILED: Grass/Memory is out of scope")
        failures += 1
    if not in_scope(ROOT / "Tests" / "Memory" / "Loans.lean"):
        print("  SELF-TEST FAILED: Tests/Memory is out of scope")
        failures += 1
    if in_scope(ROOT / "Grass" / "ISA" / "X86" / "Decode.lean"):
        print("  SELF-TEST FAILED: Grass/ISA is in scope")
        failures += 1
    if in_scope(ROOT / "Grass" / "Process" / "Bag.lean"):
        print("  SELF-TEST FAILED: Grass/Process is in scope")
        failures += 1
    if scope_is_covered(DECLARED_IN, ("Tests",)):
        print("  SELF-TEST FAILED: a SCOPE subtree on disk reached no file")
        failures += 1

    if failures:
        print(f"fixture audit self-test: {failures} failure(s)")
        return 1
    print("fixture audit self-test: all cases discriminate as documented")
    return 0


# The options this gate accepts. A misspelt flag used to be ignored: `--self-tset`
# and `--inertt` both ran the ordinary check and printed its success line at exit 0,
# so a reviewer sweeping a mode across the gates got a pass from a tool that never
# ran it. Review did exactly that in the round that found this, and one of the seven
# gates had no `--inert` implementation at all -- which is invisible when an unknown
# flag is a no-op and obvious the moment it is an error.
KNOWN_OPTIONS = {"--self-test", "--inert"}


def main() -> int:
    unknown = [arg for arg in sys.argv[1:] if arg not in KNOWN_OPTIONS]
    if unknown:
        print("unknown option(s): " + " ".join(unknown), file=sys.stderr)
        print("known: " + ", ".join(sorted(KNOWN_OPTIONS)), file=sys.stderr)
        return 2
    # The scope floor, before anything else runs. `SCOPE` is a coverage claim and
    # review showed it was one nothing checked: dropping a single token from it
    # switched this gate off for the memory layer and it printed its success line.
    uncovered_scope = scope_is_covered(DECLARED_IN, ("Tests",))
    if uncovered_scope:
        print(chr(10).join(uncovered_scope))
        print(chr(10) + "SCOPE names a subtree that reached no file. Widen the"
              " globs or correct SCOPE -- a gate that scans nothing passes.")
        return 1
    if "--self-test" in sys.argv:
        return self_test()
    if "--inert" in sys.argv:
        declared = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                    for path in DECLARED_IN}
        used = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                for path in USED_IN}
        inert = inert_entries(declared, used)
        if inert:
            print("allowlist entries that suppress nothing: " + ", ".join(inert))
            print("Delete them, or say why the entry is kept with no effect.")
        else:
            print("fixture audit: every allowlist entry suppresses a report")
        return 0
    declared = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                for path in DECLARED_IN}
    used = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
            for path in USED_IN}
    if not declared:
        print(f"fixture audit: no sources found under {ROOT / 'Tests'}", file=sys.stderr)
        return 1
    reported = analyse(declared, used)
    if reported:
        print("\n".join(reported))
        print("\nfixture audit: states built for a claim that no longer exists\n")
        print(
            f"{len(reported)} unused fixture(s). Use one, delete it, or add it to "
            "ALLOWED with the reason it is carried."
        )
        return 1
    print(
        "fixture audit: every Tests/ definition is used somewhere (a lexical check; "
        "see the module docstring for what it does not cover)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
