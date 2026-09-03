#!/usr/bin/env python3
"""Report calls to an authority-map door from outside the modules allowed to call it.

`docs/MEMORY_MODEL.md` §3 makes the authority map the authoritative borrowing state,
and `Grass/Memory/State.lean` seals it: the field is private, the constructor is
private, and five checked doors — `issue?`, `returnGrant?`, `splitGrant?`,
`joinGrants?`, `transferGrant?` — are the only ways to change it. Four times on this
branch a *second* way in was found instead of the first being reused, and the last one
was reachable through `step`.

**What this checks, exactly.** For every `.lean` source under `Grass/`, with block
comments, line comments and string literals blanked out, it reports any application of
a door name from a module that door's entry in `DOORS` does not allow. A door name
counts as applied when it appears as `.door` or `MemoryState.door` followed by an
argument or by the end of the line — so `state.issue? id grant` is a call, so is
`id grant |> state.issue?`, so is a call whose arguments wrap to the next line, and
`MemoryState.issue?` named in a `simp` set or after an `unfold` is not.

The doors are the five that change the map plus the two effect appliers, and the
allowed callers differ: only the two modules that own the field may reach the map's
doors, while the transition may reach `applyAuthorityDelta?` and
`applyAuthorityEffect?`, because that is the one place the acting context is not the
caller's to choose.

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
- A line that both names a door in a tactic *and* applies one is missed, because the
  naming tactic is detected positionally: a tactic word before the door on the line
  silences it. That is the price of not reporting every proof about a door. The
  positional rule is not cosmetic — matching the tactic anywhere on the line meant an
  argument named `delta` silenced a real call to `applyAuthorityDelta?`, which the
  self-test caught.
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

# The doors, and the modules each may be called from. `returnLoan?` is
# `Grass/Memory/Loan.lean`'s §3-named wrapper and delegates to `returnGrant?`; it is a
# door by the same argument.
#
# `applyAuthorityDelta?` and `applyAuthorityEffect?` are doors too, and the first
# version of this file left them out. Review made the omission concrete: the argument
# that an `actor` parameter on `issue?` would be worthless — a caller free to pass
# anything passes `grant.lender` — applies verbatim to `applyAuthorityDelta?`'s
# `actor`, which is caller-chosen everywhere except the one `performAccess` site where
# it is `d.context`. Three real map-changing definitions were added to
# `Grass/Op/LoanAuthority.lean`, one routed through `applyAuthorityDelta?` with
# `grant.lender` as its actor, and this tool printed its green line.
#
# So the effect appliers are guarded too, and their allowed callers are the module
# that owns them and the transition — which is the only place the actor is not the
# caller's to choose.
MAP_OWNERS = {"Grass/Memory/State.lean", "Grass/Memory/Loan.lean"}
DOORS = {
    "issue?": MAP_OWNERS,
    "returnGrant?": MAP_OWNERS,
    "returnLoan?": MAP_OWNERS,
    "splitGrant?": MAP_OWNERS,
    "joinGrants?": MAP_OWNERS,
    "transferGrant?": MAP_OWNERS,
    "applyAuthorityDelta?": {"Grass/Memory/State.lean", "Grass/Op/Step.lean"},
    "applyAuthorityEffect?": {"Grass/Memory/State.lean", "Grass/Op/Step.lean"},
    # `alias` changes which allocations name the same bytes, which is an authority
    # question -- every rule in the layer keys on `SharesBytes`. It is deliberately
    # *not* an `Option`-returning door (see its own docstring), which is exactly why
    # it belongs here: the first version of this file left it out, and review added a
    # real `Grass/Op/LoanAuthority.lean` definition calling it and watched the audit
    # print its green line.
    "alias": MAP_OWNERS,
}

BLOCK = re.compile(r"/-.*?-/", re.DOTALL)
LINE = re.compile(r"--.*?$", re.MULTILINE)
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


# A tactic that names a declaration without applying it. `unfold f at h` was reported
# as a call by the first version, which its own docstring said it would not be.
NAMING_TACTIC = re.compile(r"\b(?:unfold|simp|simp_all|rw|delta|fold|exact|apply)\b")


def blank(match: "re.Match[str]") -> str:
    """Replace a match with as many newlines as it spanned, keeping line numbers."""
    return "\n" * match.group(0).count("\n")


def strip(source: str) -> str:
    """Blank out block comments, line comments and string literals, keeping the line
    structure.

    The first version deleted them, so every report pointed at the wrong line of a
    real file: a control call on line 219 of `Grass/Op/LoanAuthority.lean` was
    reported as line 106. The self-test never noticed, because seeded sources have no
    block comments — so this function now preserves newlines and the self-test seeds
    one.
    """
    return LINE.sub("", STRING.sub('""', BLOCK.sub(blank, source)))


def applications(source: str, door: str) -> list[int]:
    """The 1-based line numbers where `door` appears in applied position."""
    # `.door` or `Namespace.door`, then an argument: anything that is not a closing
    # delimiter, a comma, or the end of the line. Accepting end-of-line catches the
    # `|>` form and a call whose arguments wrap, both of which the first version
    # missed.
    pattern = re.compile(
        r"(?:\.|\b[A-Za-z_][A-Za-z0-9_.']*\.)" + re.escape(door)
        + r"(?:[ \t]+(?![,)\]}])|[ \t]*$)"
    )
    found = []
    for number, line in enumerate(strip(source).splitlines(), start=1):
        match = pattern.search(line)
        if not match:
            continue
        # `unfold MemoryState.issue?`, `simp [MemoryState.issue?]`, `exact
        # MemoryState.issue?_eq_none_of_absent h`: named inside a proof, not applied
        # in a definition. The tactic has to come *before* the door on the line, or
        # an argument named `delta` or `fold` would silence a real call — which it
        # did, and the self-test caught it.
        if any(tactic.end() <= match.start() for tactic in NAMING_TACTIC.finditer(line)):
            continue
        found.append(number)
    return found


def analyse(sources: dict[str, str]) -> list[str]:
    """Report door applications from modules not allowed to make them."""
    reported = []
    for name in sorted(sources):
        for door, allowed in DOORS.items():
            if name in allowed:
                continue
            for number in applications(sources[name], door):
                reported.append(
                    f"  {name}:{number}: calls `{door}` from outside the modules that "
                    "own the authority map"
                )
    return reported


def self_test() -> int:
    failures = 0
    # A module allowed for no door, so one seeded case works for all of them.
    OUTSIDE = "Grass/Op/LoanAuthority.lean"
    call = "def f (s : MemoryState) := s.issue? id grant\n"

    if not analyse({OUTSIDE: call}):
        print("  SELF-TEST FAILED: a door call from a disallowed module is not reported")
        failures += 1

    if analyse({"Grass/Memory/State.lean": call}):
        print("  SELF-TEST FAILED: a door call from an allowed module is reported")
        failures += 1

    commented = "/-- `s.issue? id grant` is what a caller writes. -/\ndef f := 1\n"
    if analyse({OUTSIDE: commented}):
        print("  SELF-TEST FAILED: a door named in a docstring is reported")
        failures += 1

    mentioned = "theorem t : True := by simp [MemoryState.issue?]\n"
    if analyse({OUTSIDE: mentioned}):
        print("  SELF-TEST FAILED: a door named in a simp set is reported")
        failures += 1

    unfolded = "theorem t : True := by\n  unfold MemoryState.issue?\n"
    if analyse({OUTSIDE: unfolded}):
        print("  SELF-TEST FAILED: a door named by `unfold` is reported")
        failures += 1

    # Review found this one: the docstring said a door named by `unfold` is not
    # reported, and the `at h` form was, because the pattern only needed a following
    # space.
    unfolded_at = "theorem t : True := by\n  unfold MemoryState.issue? at h\n"
    if analyse({OUTSIDE: unfolded_at}):
        print("  SELF-TEST FAILED: `unfold X at h` is reported as a call")
        failures += 1

    # And this one: reports numbered the stripped source, so every line number from a
    # real file was wrong.
    offset = "/-\na block comment\nspanning three lines\n-/\n" + call
    reports = analyse({OUTSIDE: offset})
    if not reports or ":5:" not in reports[0]:
        print("  SELF-TEST FAILED: the reported line number does not survive a block "
              f"comment above the call: {reports}")
        failures += 1

    # And these two: a call written backwards, and one whose arguments wrap.
    piped = "def f (s : MemoryState) := id grant |> s.issue?\n"
    if not analyse({OUTSIDE: piped}):
        print("  SELF-TEST FAILED: a `|>` call is not reported")
        failures += 1

    wrapped = "def f (s : MemoryState) :=\n  s.issue?\n    id grant\n"
    if not analyse({OUTSIDE: wrapped}):
        print("  SELF-TEST FAILED: a call whose arguments wrap is not reported")
        failures += 1

    for door in DOORS:
        if not analyse({OUTSIDE: f"def f (s : MemoryState) := s.{door} a b\n"}):
            print(f"  SELF-TEST FAILED: `{door}` is not scanned for")
            failures += 1

    # The appliers are doors with a wider allowlist: the transition may call them,
    # because that is the one place the actor is not the caller's to choose.
    applier = "def f (s : MemoryState) := s.applyAuthorityDelta? actor delta\n"
    if analyse({"Grass/Op/Step.lean": applier}):
        print("  SELF-TEST FAILED: the transition may call an applier and is reported")
        failures += 1
    if not analyse({OUTSIDE: applier}):
        print("  SELF-TEST FAILED: an applier called from elsewhere is not reported")
        failures += 1

    # Documented blind spot: lexical, so a door reached through a binding is invisible.
    # Asserted so it cannot quietly become coverage.
    indirect = "def door := MemoryState.issue?\ndef f (s : MemoryState) := door s a b\n"
    if len(analyse({OUTSIDE: indirect})) > 1:
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
