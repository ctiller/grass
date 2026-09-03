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
DECLARED_IN = sorted((ROOT / "Tests").rglob("*.lean"))
USED_IN = (DECLARED_IN + sorted((ROOT / "Grass").rglob("*.lean"))
           + sorted((ROOT / "Tools").rglob("*.lean")))

# Lean identifiers here use subscript digits and primes as well as ASCII.
IDENT = r"[A-Za-z_][A-Za-z0-9_'₀-₉¹²³]*"
DEFINITION = re.compile(r"^(?:private\s+|protected\s+)?def\s+(" + IDENT + r")", re.MULTILINE)
BLOCK = re.compile(r"/-.*?-/", re.DOTALL)
LINE = re.compile(r"--.*?$", re.MULTILINE)
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')

# Fixtures deliberately carried without a user, each with its reason. The two entries
# this tool was written against -- `currentProv` and `lentThenReused` in
# `Tests/Memory/Loans.lean` -- were deleted rather than listed.
ALLOWED: set[str] = {
    # Consumed by an environment-walking audit rather than by name.
    # `Tools/AxiomAudit.lean` and `audit-trust.ps1` discover `VerifiedProgram`
    # producers from their *types* and report on them -- both of these appear in the
    # audit's own output -- so no source mentions them and this tool cannot see the
    # consumer. They belong to another owner's module and the shape is deliberate:
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
    return LINE.sub("", STRING.sub('""', BLOCK.sub("", source)))


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


def self_test() -> int:
    failures = 0

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

    if failures:
        print(f"fixture audit self-test: {failures} failure(s)")
        return 1
    print("fixture audit self-test: all cases discriminate as documented")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
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
