#!/usr/bin/env python3
"""Report calls to an authority-map door from outside the modules allowed to call it.

`docs/MEMORY_MODEL.md` §3 makes the authority map the authoritative borrowing state,
and `Grass/Memory/State.lean` seals it: the field is private, the constructor is
private, and five checked doors — `issue?`, `returnGrant?`, `splitGrant?`,
`joinGrants?`, `transferGrant?` — are the only ways to change it. Four times on this
branch a *second* way in was found instead of the first being reused, and the last one
was reachable through `step`.

**What this checks, exactly.** For every `.lean` source under `Grass/`, with block
comments, line comments and string literals stripped, it reports any application of a
door name that is not in `ALLOWED_CALLERS`. A door name counts as applied when it
appears as `.door` or `MemoryState.door` followed by something other than a closing
delimiter — so `state.issue? id grant` is a call and `MemoryState.issue?` named in a
`simp` set or an `unfold` is not.

The rule it enforces is narrow and worth stating precisely, because the obvious
stronger rule is wrong. `MemoryState.issue?` takes no acting context: it reads the
lender from the grant it is given. So "the acting context must be the lender it
names" cannot be checked inside it — a caller holding the grant would satisfy an
`actor` parameter by passing `grant.lender`, which is a gate closed with the thing
being gated. The check has content only where the actor comes from somewhere the
caller does not choose, which is `AccessDescriptor.context`, and that is where
`MemoryState.applyAuthorityDelta?` puts it. This audit is the guard that keeps every
`Grass/` path going through there: a future caller reaching a door directly would
lend as any lender it liked, and `MayLend` would stop it conjuring authority but not
stop it stripping another context's exclusivity.

**What it does not check**, stated because three tools in this directory have been
corrected for advertising a stronger reading:

- It is lexical and namespace-blind, exactly as `ConsultedAudit.py` and
  `ReachabilityAudit.py` are. A door name reached through an abbreviation, a `let`
  binding, an `open`, or a function that returns the door is invisible. So is a
  method of the same name on some other type, in the other direction: it would be
  reported.
- It says nothing about `Tests/`, which is not scanned. Fixtures build states by
  calling the doors directly, and that is what a fixture is for; `issue?`'s
  unverified `lender` is a claim a fixture makes while setting up.
- A clean run means no `Grass/` module outside the allowlist *mentions* a door in
  applied position. It is not evidence that the doors are otherwise sealed — the
  private field and private constructor are what do that, and no audit here can see
  privacy.

`--self-test` seeds each class this file claims to catch and each near-miss it must
stay quiet on. Run it after changing the scanner.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCES_IN = sorted((ROOT / "Grass").rglob("*.lean"))

# The doors. `returnLoan?` is `Grass/Memory/Loan.lean`'s §3-named wrapper and
# delegates to `returnGrant?`; it is a door by the same argument.
DOORS = (
    "issue?",
    "returnGrant?",
    "returnLoan?",
    "splitGrant?",
    "joinGrants?",
    "transferGrant?",
)

# Where a door may be called from, with the reason.
ALLOWED_CALLERS = {
    # Declares all five and composes them into `applyAuthorityDelta?`, which is the
    # one place an acting context exists to check a delta against.
    "Grass/Memory/State.lean",
    # `returnLoan?` is declared here and delegates; §3's laws are stated here over
    # the door they no longer define.
    "Grass/Memory/Loan.lean",
}

BLOCK = re.compile(r"/-.*?-/", re.DOTALL)
LINE = re.compile(r"--.*?$", re.MULTILINE)
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


def strip(source: str) -> str:
    """Remove block comments, line comments and string literals."""
    return LINE.sub("", STRING.sub('""', BLOCK.sub("", source)))


def applications(source: str, door: str) -> list[int]:
    """The 1-based line numbers where `door` appears in applied position."""
    # `.door` or `Namespace.door`, then something that is not a delimiter, a comma,
    # or the end of a line: an argument.
    pattern = re.compile(
        r"(?:\.|\b[A-Za-z_][A-Za-z0-9_.']*\.)" + re.escape(door) + r"[ \t]+(?![,)\]}])"
    )
    found = []
    for number, line in enumerate(strip(source).splitlines(), start=1):
        if pattern.search(line):
            found.append(number)
    return found


def analyse(sources: dict[str, str]) -> list[str]:
    """Report door applications from modules not allowed to make them."""
    reported = []
    for name in sorted(sources):
        if name in ALLOWED_CALLERS:
            continue
        for door in DOORS:
            for number in applications(sources[name], door):
                reported.append(
                    f"  {name}:{number}: calls `{door}` from outside the modules that "
                    "own the authority map"
                )
    return reported


def self_test() -> int:
    failures = 0
    call = "def f (s : MemoryState) := s.issue? id grant\n"

    if not analyse({"Grass/Op/Step.lean": call}):
        print("  SELF-TEST FAILED: a door call from a disallowed module is not reported")
        failures += 1

    if analyse({"Grass/Memory/State.lean": call}):
        print("  SELF-TEST FAILED: a door call from an allowed module is reported")
        failures += 1

    commented = "/-- `s.issue? id grant` is what a caller writes. -/\ndef f := 1\n"
    if analyse({"Grass/Op/Step.lean": commented}):
        print("  SELF-TEST FAILED: a door named in a docstring is reported")
        failures += 1

    mentioned = "theorem t : True := by simp [MemoryState.issue?]\n"
    if analyse({"Grass/Op/Step.lean": mentioned}):
        print("  SELF-TEST FAILED: a door named in a simp set is reported")
        failures += 1

    unfolded = "theorem t : True := by\n  unfold MemoryState.issue?\n"
    if analyse({"Grass/Op/Step.lean": unfolded}):
        print("  SELF-TEST FAILED: a door named by `unfold` is reported")
        failures += 1

    for door in DOORS:
        if not analyse({"Grass/Op/Step.lean": f"def f (s : MemoryState) := s.{door} a b\n"}):
            print(f"  SELF-TEST FAILED: `{door}` is not scanned for")
            failures += 1

    # Documented blind spot: lexical, so a door reached through a binding is invisible.
    # Asserted so it cannot quietly become coverage.
    indirect = "def door := MemoryState.issue?\ndef f (s : MemoryState) := door s a b\n"
    if len(analyse({"Grass/Op/Step.lean": indirect})) > 1:
        print("  SELF-TEST FAILED [indirection blind spot]: this now discriminates; "
              "update the module docstring, which documents it as unhandled")
        failures += 1

    if failures:
        print(f"door audit self-test: {failures} failure(s)")
        return 1
    print("door audit self-test: all cases discriminate as documented")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    sources = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
               for path in SOURCES_IN}
    if not sources:
        print(f"door audit: no sources found under {ROOT / 'Grass'}", file=sys.stderr)
        return 1
    reported = analyse(sources)
    if reported:
        print("\n".join(reported))
        print("\ndoor audit: the authority map changed from outside its own modules\n")
        print(
            f"{len(reported)} call site(s). Route the change through "
            "`MemoryState.applyAuthorityDelta?`, which checks it against an acting "
            "context, or add the module to ALLOWED_CALLERS with the reason."
        )
        return 1
    print(
        "door audit: every authority-map change under Grass/ goes through the modules "
        "that own the map (a lexical check; see the module docstring for what it does "
        "not cover)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
