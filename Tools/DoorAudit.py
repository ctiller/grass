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

The doors are the five that change the grant map, the two effect appliers, the
aliasing declaration, the authority minter, and the three allocation-table mutators --
thirteen, which `DOORS` is and `self_test` now asserts. This sentence said "the five
plus the two" for as long as there have been thirteen, in the file whose subject is
which doors exist; each of the six it omitted is defended at length by a comment in
`DOORS` itself. The allowed callers differ per door: only the two modules that own the field may reach the map's
doors, while the transition may reach `applyAuthorityEffect?`, because that is the one
place the acting context is not the caller's to choose.

`applyAuthorityDelta?` is *not* on the wider list, and it was, with that same reason
attached. The transition applies the effect in five places and the delta in none, so
the allowance was a widened permission granted for no caller -- on the door whose whole
purpose is the actor check. Review removed it and nothing changed, which is how it was
found.

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
# `Grass/Op/Facets.lean`, one routed through `applyAuthorityDelta?` with
# `grant.lender` as its actor, and this tool printed its green line.
#
# So the effect appliers are guarded too, and their allowed callers are the module
# that owns them and the transition — which is the only place the actor is not the
# caller's to choose.
# **An allowance is per (door, module), and a blanket set was granting eight of them
# to no caller at all.** `MAP_OWNERS` gave `Grass/Memory/Loan.lean` reach into four of
# `State.lean`'s doors it never calls, and `State.lean` reach into `Loan.lean`'s one
# door it never calls. That is the same defect this file records finding for
# `applyAuthorityDelta?` and `Grass/Op/Step.lean` below -- a widened permission granted
# for no caller -- repeated five times by a shared constant, which is how one decision
# became five.
#
# The rule now: a door's *declaring* module is always allowed, because a door that its
# own module may not call is not a door; a *cross-module* allowance must have a caller,
# and `--inert` reports one that does not. `Loan.lean` calls `issue?` and
# `returnGrant?`, and that is the whole of the cross-module traffic.
MAP_OWNERS = {"Grass/Memory/State.lean", "Grass/Memory/Loan.lean"}
DOORS = {
    "issue?": MAP_OWNERS,
    "returnGrant?": MAP_OWNERS,
    "returnLoan?": {"Grass/Memory/Loan.lean"},
    "splitGrant?": {"Grass/Memory/State.lean"},
    "joinGrants?": {"Grass/Memory/State.lean"},
    "transferGrant?": {"Grass/Memory/State.lean"},
    # `Grass/Op/Step.lean` is allowed the *effect* and not the *delta*: it applies
    # `applyAuthorityEffect?` in five places and `applyAuthorityDelta?` in none. The
    # allowance was on both, with a reason true only of the second -- "the transition
    # may reach `applyAuthorityDelta?` … because that is the one place the acting
    # context is not the caller's to choose" -- so the door whose whole purpose is the
    # actor check carried a widened permission granted for no caller. Removing it
    # changed nothing, which is how review found it.
    "applyAuthorityDelta?": {"Grass/Memory/State.lean"},
    "applyAuthorityEffect?": {"Grass/Memory/State.lean", "Grass/Op/Step.lean"},
    # `alias` changes which allocations name the same bytes, which is an authority
    # question -- every rule in the layer keys on `SharesBytes`. It is deliberately
    # *not* an `Option`-returning door (see its own docstring), which is exactly why
    # it belongs here: the first version of this file left it out, and review added a
    # real `Grass/Op/Facets.lean` definition calling it and watched the audit
    # print its green line.
    "alias": {"Grass/Memory/State.lean"},
    # `ProtocolAuthority.mintedBy` is the one door onto the value every ledger delta
    # carries, and it is public, total and unconditioned: review minted authority for
    # a protocol out of a string in a module that owns nothing and discharged another
    # family's duty with it. `AdmittedVocabulary.protocols` is what checks the claim
    # now, and this keeps a `Grass/` caller from minting outside the module that
    # declares it. `Tests/` is not scanned, and a fixture minting authority to build a
    # state is exactly what a fixture is for.
    "mintedBy": {"Grass/Obligation/Core.lean"},
    # The byte mutators. §1's chokepoint sentence names bytes before authority --
    # "raw mutation of memory bytes, initialization, permissions, provenance, or race
    # state outside that interface is prohibited" -- and this audit guarded only the
    # authority half until review pointed that out. `write` is public and unbounded by
    # the record's extent; `allocate?` and `tearDown?` change permission, liveness,
    # extent and placement.
    #
    # `MemoryState.write` is deliberately *not* listed, and the reason is this tool's
    # documented namespace blindness rather than a judgement about the function.
    # `write` is also `ByteStore.write`, used throughout `Grass/Memory/ByteStore.lean`
    # and `State.lean`, and `.write` is an `AccessIntent` constructor -- adding the
    # name produced twenty-six reports, none of them a call to the mutator. Guarding
    # it needs elaboration, not a regex. Its two `Grass/` callers today are
    # `MemoryState.commit` and `Shape.lean`'s `writeField`, and
    # `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records that the second is unbounded
    # by the allocation and safe only for want of callers.
    "allocate?": {"Grass/Memory/State.lean"},
    "allocateAll?": {"Grass/Memory/State.lean"},
    "tearDown?": {"Grass/Memory/State.lean"},
}

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


# A tactic that names a declaration without applying it. `unfold f at h` was reported
# as a call by the first version, which its own docstring said it would not be.
#
# `exact` and `apply` were in this list and are the two that do not belong: they are
# the tactics that *do* apply what they name, so `def f ... := by exact s.alias a b`
# -- a definition written in tactic mode -- was silent while the identical term-mode
# definition beside it was reported. The stated coverage is "any application of one
# of the five doors", and review appended both forms to a real module allowed for
# neither and got one report. Nothing is lost by dropping them, because the naming
# forms these two tactics take do not match the application pattern anyway: `exact
# MemoryState.issue?_eq_none_of_absent h` continues the name past the `?` with a
# `_`, and `simp [MemoryState.issue?]` closes with a `]`. `self_test` seeds both
# directions, because dropping a name from this list is a widening and a narrowing
# at once.
NAMING_TACTIC = re.compile(r"\b(?:unfold|simp|simp_all|rw|delta|fold)\b")


def blank(match: "re.Match[str]") -> str:
    """Replace a match with as many newlines as it spanned, keeping line numbers."""
    return "\n" * match.group(0).count("\n")


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
    """Blank out block comments, line comments and string literals, keeping the line
    structure.

    The first version deleted them, so every report pointed at the wrong line of a
    real file: a control call on line 219 of `Grass/Op/Facets.lean` was
    reported as line 106. The self-test never noticed, because seeded sources have no
    block comments — so this function now preserves newlines and the self-test seeds
    one.
    """
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


TACTIC_OPENER = re.compile(r"(?:^|\bby\b|;|<;>|·|\|)[ \t]*$")


def is_tactic_position(line: str, tactic: "re.Match[str]") -> bool:
    """Whether `tactic` occurs where a tactic can begin.

    A tactic starts a line, or follows `by`, `;`, `<;>`, a focus dot, or a match
    alternative bar. A word in a binder list or an argument position does not, which
    is what stops `(delta : AuthorityDelta)` silencing the call that follows it.
    """
    return TACTIC_OPENER.search(line[: tactic.start()]) is not None


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
        # in a definition. The tactic has to come *before* the door on the line, and
        # has to be where a tactic can start — the beginning of the line, or after
        # `by`, `;`, `<;>` or a focus dot.
        #
        # Requiring only "earlier on the line" was the bug, and the comment here said
        # that requirement *was* the fix: a binder named `delta` is earlier on the
        # line than the call it precedes, so `def f (delta : AuthorityDelta) := …
        # applyAuthorityDelta? actor delta` was silent — which is the shape of
        # `MemoryState.applyAuthorityDelta?`'s own signature. Review appended three
        # such definitions to a module allowed for no door and only the control was
        # reported. `self_test` now seeds that line.
        if any(is_tactic_position(line, tactic) and tactic.end() <= match.start()
               for tactic in NAMING_TACTIC.finditer(line)):
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
    OUTSIDE = "Grass/Op/Facets.lean"
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

    # Review found this one: a binder named after a tactic is *earlier on the line*
    # than the call that follows it, so the positional rule alone silenced a real
    # call -- and the comment above the rule claimed that positioning was the fix.
    # This is the shape of `applyAuthorityDelta?`'s own signature.
    binder = "def f (s : MemoryState) (delta : AuthorityDelta) := s.issue? id grant\n"
    if not analyse({OUTSIDE: binder}):
        print("  SELF-TEST FAILED: a binder named `delta` silences a real door call")
        failures += 1

    # Review found this one: `exact` and `apply` were treated as naming tactics, so a
    # definition written in tactic mode applied a door invisibly while the term-mode
    # form beside it was reported. The guard's stated coverage is "any application".
    tactic_def = "def f (s : MemoryState) := by exact s.issue? id grant\n"
    if not analyse({OUTSIDE: tactic_def}):
        print("  SELF-TEST FAILED: a door applied by `exact` in a definition is not "
              "reported")
        failures += 1

    applied_def = "def f (s : MemoryState) := by apply s.issue?\n"
    if not analyse({OUTSIDE: applied_def}):
        print("  SELF-TEST FAILED: a door applied by `apply` in a definition is not "
              "reported")
        failures += 1

    # And the other direction: dropping the two names must not start reporting the
    # forms they were listed for, which is what makes the change safe rather than a
    # trade of one blind spot for a false positive.
    named_lemma = "theorem t : True := by exact MemoryState.issue?_eq_none_of_absent h\n"
    if analyse({OUTSIDE: named_lemma}):
        print("  SELF-TEST FAILED: `exact` naming a door's lemma is reported as a call")
        failures += 1

    # The door set's own size, because the module docstring named it and went stale:
    # it said "the five that change the map plus the two effect appliers" for as long as
    # there have been thirteen. A number in a comment is adjudicated by nothing; this is
    # the cheapest place to put one that is.
    if len(DOORS) != 13:
        print(f"  SELF-TEST FAILED: DOORS has {len(DOORS)} entries and the module "
              "docstring says thirteen -- update both together")
        failures += 1

    # A quote in a *line comment* opened a string in the scanner's eyes and blanked
    # every line down to the next quote, real code included. Review appended a door
    # call between two such comments and all nine gates stayed green. `STRING` runs
    # first and cannot span lines now; this is that case, seeded.
    quote = chr(34)
    quoted = ("-- the ABI" + chr(39) + "s " + quote + "shadow space" + chr(10)
              + "def f (s : MemoryState) := s.issue? id grant" + chr(10)
              + "-- registers the callee " + quote + "saves" + chr(10))
    if not analyse({OUTSIDE: quoted}):
        print("  SELF-TEST FAILED: a quote in a line comment hides a real door call")
        failures += 1

    # A `/-` inside a *line comment* used to open a block for the old regex
    # stripper, which then swallowed every line down to the next `-/` -- real code
    # included. Review hid a real `alias` call behind one and all nine gates stayed
    # green, which is the same demonstration that put `alias` in `DOORS`.
    hidden = ("-- a note mentioning /- something" + chr(10)
              + "def f (s : MemoryState) := s.issue? id grant" + chr(10)
              + "/- an ordinary closing note. -/" + chr(10))
    if not analyse({OUTSIDE: hidden}):
        print("  SELF-TEST FAILED: a `/-` in a line comment hides a real door call")
        failures += 1

    # And the other direction: a nested block comment must stay a comment all the
    # way to its own closing `-/`, not to the first one.
    nested = ("/- outer /- inner -/ def f (s : MemoryState) := s.issue? id g -/"
              + chr(10))
    if analyse({OUTSIDE: nested}):
        print("  SELF-TEST FAILED: a call inside a nested block comment is reported")
        failures += 1

    focused = "theorem t : True := by\n  constructor <;> simp [MemoryState.issue?]\n"
    if analyse({OUTSIDE: focused}):
        print("  SELF-TEST FAILED: a door named in a chained simp set is reported")
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

    # The *effect* applier is the door with a wider allowlist: the transition may
    # call it, because that is the one place the actor is not the caller's to choose.
    applier = "def f (s : MemoryState) := s.applyAuthorityEffect? actor effect\n"
    if analyse({"Grass/Op/Step.lean": applier}):
        print("  SELF-TEST FAILED: the transition may call the effect applier and is "
              "reported")
        failures += 1

    # And the *delta* applier is not: the transition calls it nowhere, so the
    # allowance it used to carry was permission for no caller.
    delta_applier = "def f (s : MemoryState) := s.applyAuthorityDelta? actor delta\n"
    if not analyse({"Grass/Op/Step.lean": delta_applier}):
        print("  SELF-TEST FAILED: the transition may not call the delta applier and "
              "is not reported")
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
        # Which (door, module) allowances permit no caller. Four sibling tools grew
        # this check after being found with dead allowlist entries; this table was
        # the fifth and had none, and review then found eight dead pairs -- five of
        # them created at once by a shared constant.
        #
        # A door's own declaring module is exempt from the report: a door its own
        # module may not call is not a door, so that allowance is structural rather
        # than a claim about a caller. Everything else must have one.
        declared = {}
        for path in sorted(ROOT.joinpath("Grass").rglob("*.lean")):
            text = path.read_text(encoding="utf-8")
            for door in DOORS:
                if re.search(r"^def %s\b" % re.escape(door), text, re.MULTILINE):
                    declared[door] = path.relative_to(ROOT).as_posix()
        bodies = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                  for path in sorted(ROOT.joinpath("Grass").rglob("*.lean"))}
        dead = []
        for door, allowed in sorted(DOORS.items()):
            for module in sorted(allowed):
                if declared.get(door) == module:
                    continue
                text = bodies.get(module, "")
                if not applications(text, door):
                    dead.append("%s <- %s" % (door, module))
        if dead:
            print("allowances that permit no caller: " + ", ".join(dead))
            print("Narrow them, or say why the allowance is kept with no caller.")
        else:
            print("door audit: every cross-module allowance has a caller")
        return 0
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
            "context, or add the module to the door's entry in DOORS with the "
            "reason it is allowed."
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
