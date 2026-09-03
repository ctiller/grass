#!/usr/bin/env python3
"""Report inductive constructors nothing outside their own declaration builds.

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 asks for this in its own words:

    Nothing enforces that every `AuthorityState` constructor stays reachable. Four
    fixtures exhibit one each. A fifth constructor, or a change that made one
    unreachable, would be caught by a reader and not by a gate.

That gap is not hypothetical. `AuthorityState` carried `sharedImmutable`,
`unavailable` and `atomicShared` with nothing building any of them, so every theorem
about them held of a term no state could reach — which reads as coverage and is not.
Two were made reachable and one was deleted; the same thing can happen again, and
`Tools/ConsultedAudit.py` cannot see it, because it scans structure fields and this
is about sum constructors.

**What this checks, exactly.** For each `inductive T` under `Grass/`, it collects the
constructor names on `| ctor` lines. It then searches the comment- and
string-stripped sources of `Grass/` and `Tests/` for a construction site outside the
declaration itself: either the qualified `T.ctor`, or a bare `.ctor` that is not in a
match-arm position. A constructor with none is reported.

**What it does not check**, stated because two tools in this directory have been
corrected for advertising a stronger reading:

- Dot notation is namespace-blind, exactly as in `ConsultedAudit.py`. Two inductives
  with a constructor of the same name are indistinguishable, so building one
  satisfies the other. Lean would have to be elaborated to do better.
- It cannot tell a construction in live code from one in dead code, nor "built" from
  "built only by a fixture that asserts nothing about it".
- It cannot see a constructor produced by a generic function returning `T`, or by
  `deriving`, or by a `default` field value spelled without the constructor's name.
- Match arms are excluded by a heuristic: a `.ctor` is a *pattern* if it is followed
  by `=>`, or preceded on the same line by a `|` with no `=>` between them. A
  construction written to look like that is missed, and a pattern written across
  lines may be counted as a construction — a false negative and a false positive
  respectively. The `|`-with-no-`=>` refinement is not cosmetic: without it, a
  constructor built on the value side of an arm was reported as unbuilt.
- **A constructor named in a theorem's own statement counts as built.** `theorem t
  (h : a.kind = .fence) : …` reads exactly like a construction, and it is one — the
  term `.fence` is built, to be compared against. What the tool cannot tell is
  whether anything *reachable* produces it. That is the shape it was written to
  catch, so this is the blind spot that matters most: review found
  `MemoryEvent.EventKind.fence` unconstructible by any producer, with its only
  occurrence inside a theorem about it, and this tool silent. Reaching further needs
  elaboration, not a regex.
- It cannot see a constructor of an inductive whose constructors are written flush
  left (`inductive T where` then `| a` at column zero, which is legal). That shape
  does not occur in `Grass/` today; it is one reformat away, and the scanner treats
  the `|` line as the end of the declaration.

So a clean run means every constructor's name appears somewhere that looks like a
construction. It is one cheap net over a defect this layer has hit three times in one
type, and it under-reports by design.

The allowlist is where "declared deliberately without a builder" is recorded, with a
reason per entry.

`--self-test` seeds each class this file claims to catch and each near-miss it must
stay quiet on. Run it after changing the scanner.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECLARED_IN = sorted((ROOT / "Grass").rglob("*.lean"))
BUILDERS_IN = DECLARED_IN + sorted((ROOT / "Tests").rglob("*.lean"))

INDUCTIVE = re.compile(r"^\s*(?:private\s+|protected\s+)?inductive\s+([A-Za-z_][A-Za-z0-9_.']*)")
CONSTRUCTOR = re.compile(r"^\s*\|\s*([a-z][A-Za-z0-9_']*)")
BLOCK = re.compile(r"/-.*?-/", re.DOTALL)
LINE = re.compile(r"--.*?$", re.MULTILINE)
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')

# Constructors carried without a builder, as `Inductive.constructor` pairs. Every
# entry says why.
#
# **Pairs, not bare names.** The first version was a set of bare constructor names, so
# an entry exempted *any* constructor of that name on *any* inductive — a second
# namespace-blindness, distinct from the one the scan has and worse, because it grows
# silently as the tree does. Review demonstrated a fresh unbuilt constructor going
# unreported because an unrelated type had a constructor of the same name, and found
# eight of the twenty-one entries inert.
ALLOWED = {
    # Portable ordering and scope names section 7.1 fixes. A profile picks the ones
    # its target has; the model owes all of them.
    #
    # Two groups stood here and are gone, along with five entries from this one:
    # "vocabulary an ISA or profile supplies" (`Address.symbolic`,
    # `AddressRepr.symbolic`, the three `profileSpecific`) and "terminal and
    # lifecycle vocabulary whose consumers are later milestones" (both
    # `Restartability` constructors). Every one of the twelve suppressed nothing,
    # and five of them were flatly contradicted by the tree: `Restartability`'s two
    # are a struct field default in `Grass/Memory/Access.lean` and a fixture,
    # `Atomicity.nonAtomic` is a field default in `Grass/Memory/Ordering.lean`,
    # `Address.symbolic` is built in `Tests/Memory/WellFormedClauses.lean` and
    # `AddressRepr.symbolic` in `Grass/Memory/AddressSpace.lean`. The rest were
    # silenced by this tool's own same-name blindness -- `MemoryScope.system` by an
    # unrelated `system` component, two `profileSpecific` by the third.
    #
    # `--inert` exists now, so this cannot rot back the way it did. The preamble
    # above records the same sweep being run once already, by hand, and finding
    # eight of twenty-one; the entries that grew back are why a hand sweep is not
    # enough.
    "MemoryScope.process",
    "MemoryScope.device",
    # --- Declared ahead of the milestone that builds them. Being listed here is not
    # --- "this is fine": it is the record that someone read the plan and decided,
    # --- and the reason differs per entry.
    #
    # Requirement vocabulary from another owner's modules, which arrived here by
    # merging main. `RequirementKind` declares ten constructors and nothing in the
    # tree builds one; `DemandFamily.kind`'s own docstring calls it "exact metadata
    # only", so unbuilt is consistent with its intent -- a demand provider supplies
    # the kind, and no provider exists yet. Listed rather than silenced, and
    # reported to that owner: whether a ten-name closed vocabulary with no producer
    # and no consumer is the right shape is their decision, not this branch's.
    "RequirementKind.functional",
    "RequirementKind.safety",
    "RequirementKind.concurrency",
    "RequirementKind.progress",
    "RequirementKind.termination",
    "RequirementKind.resource",
    "RequirementKind.obligation",
    "RequirementKind.diagnostic",
    "RequirementKind.applicability",
    "RequirementKind.extension",
    "RequirementOrigin.prior",
    "RequirementOrigin.external",
    # `docs/MEMORY_MODEL.md` section 7.1 makes control events part of the event
    # vocabulary; nothing in this layer mints one, because control flow is the ISA
    # owner's and the causal graph is M8's.
    "EventKind.control",
    # §7.1 requires a fence event kind and nothing can mint one: `kindOf` yields only
    # `read`, `write` and `readModifyWrite`, and `AccessIntent` has no fence form —
    # an intent that neither reads nor writes is refused by `WellFormedIn.notInert`.
    # So §7.4's "release establishes the profile's causal edge" has no event to carry
    # it. Recorded in `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2.
    "EventKind.fence",
    # `docs/OBLIGATIONS.md` section 3 requires every obligation at a terminal edge to
    # receive a disposition. M5 owns terminal accounting and does not exist, so these
    # two are named and unbuilt.
    #
    # An earlier version of this comment added "`Spikes/1_Hello_World` needs both",
    # and review checked: that directory holds `Program.lean` and `Spec.lean` and
    # neither mentions a disposition or an obligation at all. A false reason on an
    # allowlist entry is worse than none, because it reads as an argument somebody
    # made. The true reason is the first two sentences.
    #
    # The other three `Disposition` constructors are *not* listed here and are just
    # as unbuilt: they appear only in match arms and in three one-line simp theorems,
    # which this tool counts as construction. That is the blind spot its own docstring
    # calls the one that matters most, and review demonstrated it by deleting the
    # three theorems and watching all three constructors get reported.
    "Disposition.transferred",
    "Disposition.teardownAdopted",
    # The resource layer is built ahead of its consumers, which arrive at M7 and M9.
    # `Tools/ConsultedAudit.py` records the same thing about its fields.
    "ResourceLifecyclePolicy.affineTransfer",
    "ResourceLifecyclePolicy.sharedOnce",
    "ResourceLifecyclePolicy.phaseExclusive",
    "ResourceLifecyclePolicy.scopedRelease",
    "ResourceExhaustionPolicy.reject",
    "ResourceExhaustionPolicy.backpressure",
    "ResourceExhaustionPolicy.fail",
}


def scannable(text: str) -> str:
    """Strip comments and string literals, as `ConsultedAudit.py` does.

    Prose naming a constructor is not a construction of it, and this file's own
    docstring names several.
    """
    return STRING.sub('""', LINE.sub("", BLOCK.sub(" ", text)))


def constructors_in(text: str) -> list[tuple[str, str, int]]:
    """Yield (inductive, constructor, line) for every constructor in one source."""
    out: list[tuple[str, str, int]] = []
    current: str | None = None
    in_doc = False
    for number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if in_doc:
            if "-/" in stripped:
                in_doc = False
            continue
        if stripped.startswith("/-"):
            if "-/" not in stripped:
                in_doc = True
            continue
        match = INDUCTIVE.match(line)
        if match:
            current = match.group(1)
            continue
        if current is None:
            continue
        found = CONSTRUCTOR.match(line)
        if found:
            out.append((current, found.group(1), number))
            continue
        # A constructor line ends nothing. Testing for the end *first* meant an
        # inductive whose constructors are flush left — legal Lean — had every one of
        # them skipped and the tool printed a clean run.
        if stripped.startswith("deriving") or (stripped and not line.startswith(" ")):
            current = None
    return out


def builds(body: str, inductive: str, constructor: str) -> bool:
    """Whether `body` looks like it constructs `Inductive.constructor` somewhere.

    A qualified mention always counts. A bare `.ctor` counts unless it is in a
    match-arm *pattern* position: followed by `=>`, or preceded on the same line by a
    `|` with no `=>` between them.
    """
    if re.search(r"\b%s\.%s\b" % (re.escape(inductive.split(".")[-1]),
                                  re.escape(constructor)), body):
        return True
    for line in body.splitlines():
        for match in re.finditer(r"\.%s\b" % re.escape(constructor), line):
            before = line[: match.start()]
            after = line[match.end() : match.end() + 6]
            if "=>" in after:
                continue
            # A `|` earlier on the line makes this a pattern only if no `=>` has
            # intervened. `| some space => if p then [] else [.ctor x]` builds on the
            # value side of an arm, and a first version of this rule called it a
            # pattern and reported the constructor as unbuilt.
            bar = before.rfind("|")
            if bar != -1 and "=>" not in before[bar:]:
                continue
            return True
    return False


def analyse(raw: dict[str, str], builders: dict[str, str] | None = None) -> list[str]:
    """Report `path:line: Inductive.ctor` for every constructor nothing builds."""
    corpus = {name: scannable(text) for name, text in (builders or raw).items()}
    unbuilt: list[str] = []
    for name, text in raw.items():
        declaring = scannable(text)
        for inductive, constructor, line in constructors_in(text):
            if f"{inductive.split('.')[-1]}.{constructor}" in ALLOWED:
                continue
            found = False
            for other, body in corpus.items():
                # The declaration's own file counts only outside the `inductive`
                # block, which `constructors_in` already located; a `| ctor` line is
                # not a construction, and `builds` skips it for the leading `|`.
                if builds(body if other != name else declaring, inductive, constructor):
                    found = True
                    break
            if not found:
                unbuilt.append(
                    f"  {name}:{line}: {inductive}.{constructor} is declared and "
                    "nothing appears to build it"
                )
    return unbuilt


def self_test() -> int:
    """Seed each class this file claims to catch, and the near-misses it must not."""
    decl = "inductive Probe where\n  | quarry\n  | decoy\n"
    cases: list[tuple[str, dict[str, str], bool]] = [
        ("nothing builds it", {"a.lean": decl}, True),
        ("qualified construction",
         {"a.lean": decl, "b.lean": "def f : Probe := Probe.quarry\n"}, False),
        ("bare construction",
         {"a.lean": decl, "b.lean": "def f : Probe := .quarry\n"}, False),
        # A match arm is not a construction. This is the case that makes the tool
        # worth having: `AuthorityState.atomicShared` was matched on by
        # `PermitsOrdinaryWrite` and built by nothing.
        # Built on the *value* side of a match arm, which the pattern rule must not
        # mistake for the pattern side. A first version of that rule did, and
        # reported a constructor built inside an `if` in an arm body.
        ("built on the value side of an arm",
         {"a.lean": decl,
          "b.lean": "def f : Nat -> Probe\n  | 0 => .quarry\n  | _ => .decoy\n"}, False),
        ("matched but not built",
         {"a.lean": decl,
          "b.lean": "def f : Probe -> Nat\n  | .quarry => 0\n  | .decoy => 1\n"}, True),
        ("prose mentioning it",
         {"a.lean": decl, "b.lean": "/-- builds `Probe.quarry` one day -/\ndef f := 1\n"},
         True),
        ("string literal mentioning it",
         {"a.lean": decl, "b.lean": 'def f := "Probe.quarry"\n'}, True),
        # Flush-left constructors are a declaration the scanner must still see.
        ("flush-left constructors",
         {"a.lean": "inductive Probe where\n| quarry\n| decoy\n"}, True),
        # Documented blind spot, asserted: a constructor named in a theorem's own
        # statement reads as a construction, which is how `EventKind.fence` stayed
        # unreported while nothing could mint one.
        ("named only in a theorem about it",
         {"a.lean": decl,
          "b.lean": "theorem t (p : Probe) (h : p = Probe.quarry) : True := trivial\n"},
         False),
    ]
    failures = 0
    for label, sources, should_report in cases:
        reported = any("Probe.quarry" in line for line in analyse(sources))
        if reported != should_report:
            want = "reported" if should_report else "not reported"
            print(f"  SELF-TEST FAILED [{label}]: expected {want}")
            failures += 1

    # The builder corpus is a separate parameter, and no case above exercises it.
    builder_only = {"a.lean": decl}
    builders = {"a.lean": decl, "t.lean": "def f : Probe := .quarry\n"}
    if any("Probe.quarry" in line for line in analyse(builder_only, builders)):
        print("  SELF-TEST FAILED [builder corpus]: expected not reported")
        failures += 1

    # An allowlist entry must not exempt another inductive's constructor of the same
    # name. This was the first version's behaviour and it grew silently.
    global ALLOWED
    saved = ALLOWED
    ALLOWED = {"Decoy.quarry"}
    if not any("Probe.quarry" in line for line in analyse({"a.lean": decl})):
        print("  SELF-TEST FAILED [allowlist keying]: an entry for another inductive "
              "exempted this one")
        failures += 1
    ALLOWED = saved

    # Documented blind spot: namespace-blind, so another inductive's constructor of
    # the same name satisfies this one. Asserted so it cannot become silent coverage.
    other = decl + "\ninductive Decoy where\n  | quarry\n"
    if any("Probe.quarry" in line for line in
               analyse({"a.lean": other, "b.lean": "def f : Decoy := Decoy.quarry\n"})):
        print("  SELF-TEST FAILED [namespace blind spot]: this now discriminates; "
              "update the module docstring, which documents it as unhandled")
        failures += 1

    if failures:
        print(f"reachability audit self-test: {failures} failure(s)")
        return 1
    print("reachability audit self-test: all cases discriminate as documented")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    if "--inert" in sys.argv:
        # Which entries suppress nothing. `ConsultedAudit.py` grew this after review
        # found eight of its twenty-one entries inert; this tool had the same defect
        # and no way to say so, and review then found twelve of thirty-seven here.
        # A listing rather than an exit code: an inert entry is not a violation of the
        # rule this tool enforces, it is a claim about the tree that has stopped being
        # true, and the fix is to delete it.
        global ALLOWED
        declared = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                    for path in DECLARED_IN}
        builders = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                    for path in BUILDERS_IN}
        listed = sorted(ALLOWED)
        saved = ALLOWED
        ALLOWED = set()
        reported = " ".join(analyse(declared, builders))
        ALLOWED = saved
        inert = [entry for entry in listed if entry not in reported]
        if inert:
            print("allowlist entries that suppress nothing: " + ", ".join(inert))
            print("Delete them, or say why the entry is kept with no effect.")
        else:
            print("reachability audit: every allowlist entry suppresses a report")
        return 0
    declared = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                for path in DECLARED_IN}
    builders = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                for path in BUILDERS_IN}
    if not declared:
        print(f"reachability audit: no sources found under {ROOT / 'Grass'}",
              file=sys.stderr)
        return 1
    unbuilt = analyse(declared, builders)
    if unbuilt:
        print("\n".join(sorted(unbuilt)))
        print("\nreachability audit: constructors nothing builds\n")
        print(
            f"{len(unbuilt)} unbuilt constructor(s). Build one, delete it, or add it "
            "to ALLOWED with the reason it is declared."
        )
        return 1
    print(
        "reachability audit: every declared constructor appears to be built "
        "(a lexical check; see the module docstring for what it does not cover)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
