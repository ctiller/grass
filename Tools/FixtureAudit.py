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

**What this checks, exactly.** For every `def` declared under `Tests/`, it counts
occurrences of that name in the comment- and string-stripped sources of `Grass/`,
`Tests/` and `Tools/`. One occurrence is the declaration itself; zero further ones is
a report.

**What it does not check**, stated because every tool in this directory has been
corrected for advertising a stronger reading:

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
# **Scope: the modules this gate was written for.**
#
# Merging `origin/main` put three other owners' trees under these globs -- `Grass/ISA`,
# `Grass/ABI`, `Grass/Process` and their fixtures -- and this gate immediately reported
# hundreds of findings in them. Every one may be true and none is this branch's to
# judge: an allowlist entry here records that *somebody read the corpus and decided*,
# and nobody on this branch has read theirs. A gate that reports what its author cannot
# adjudicate produces a list nobody acts on, which is how an allowlist fills with
# entries that record nothing.
#
# So the scope is named rather than implied, and widening it is one edit. The honest
# statement of coverage is in the module docstring: this gate covers the memory layer,
# and the rest of the tree is not covered by anything of this kind. That has been
# reported to those owners rather than decided here.
SCOPE = ("Memory", "Obligation", "Resource", "Op", "Core", "Std", "Trust", "Semantics")


def in_scope(path) -> bool:
    """Whether a path lies in one of `SCOPE`'s subtrees, or at a tree's root."""
    parts = path.parts
    for i, part in enumerate(parts):
        if part in ("Grass", "Tests") and i + 1 < len(parts):
            return parts[i + 1].removesuffix(".lean") in SCOPE
    return True


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
BLOCK = re.compile(r"/-.*?-/", re.DOTALL)
LINE = re.compile(r"--.*?$", re.MULTILINE)
STRING = re.compile(r'"(?:[^"\\\n]|\\.)*"')

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


def strip(source: str) -> str:
    """Remove block comments, line comments and string literals."""
    return LINE.sub(blank, BLOCK.sub(blank, STRING.sub(blank, source)))


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
