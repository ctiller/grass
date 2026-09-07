#!/usr/bin/env python3
"""Report structure fields whose name is never projected anywhere.

Six rounds of adversarial review on the memory layer found eight defects that had
already passed a merge review, and all but one had the same shape: the model
carries a fact and nothing consults it. `Obligation.owner`, so any context could
discharge any duty. `Substep.faults`. `AccessIntent.isDevice`, which section 7.5
makes load-bearing.

**What this checks, exactly.** For each field name declared in a `structure`, it
searches the sources for the token `.name`. If that token never appears, the field
is reported. That is a *lexical* property and it is weaker than "nothing reads
this field" in ways worth naming, because an earlier version of this file
advertised the stronger reading and review corrected it:

- It keys on the field name, not on the declaring structure. Two structures with a
  field of the same name are indistinguishable, so a projection of one satisfies
  the other. Lean would need to be elaborated to do better; a text scan cannot.

  That also defeats the **allowlist**, which is not obvious and which review had to
  point out. `AccessDescriptor.restartability` is listed below as a genuine gap with
  no reader — and deleting the entry changes nothing, because
  `OperationFacets.restartability` is projected elsewhere and satisfies the name.
  So an allowlist entry can record a judgement the tool could never have needed, and
  the gap it documents can be unreportable. Read an entry as a note to a human, not
  as a suppression the tool relies on.
- It cannot tell a projection from a suffix that merely looks like one.
- Comments and string literals are stripped before scanning, so prose mentioning
  `.owner` no longer counts as a reader. That was a real false negative.
- A construction `name := value` is a write, not a read, and is not counted. That
  was also a real false negative: an external constructor made an unread field
  pass.

So a clean run means **no declared field name is entirely absent from the
sources**. It does not mean every field is meaningfully consumed, and it is not
evidence that the defect class is closed. It is one cheap net over a class that
six rounds of human-style review kept missing, and it under-reports by design.

The allowlist is where "carried deliberately without a reader" is recorded, with a
reason per entry. An unlisted field with no reader fails the build, so the
judgement is made once rather than rediscovered.

`--self-test` seeds each false-negative class this file claims to have closed and
asserts the tool still reports the field. Run it after changing the scanner; a
silent audit is worse than no audit, and this one was silent on its first version.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECLARED_IN = sorted((ROOT / "Grass").rglob("*.lean"))
# Readers are looked for in the fixtures too: a field a fixture projects is read,
# and excluding them made AuditViolation.class_ look inert when Tests/ reads it.
READERS_IN = DECLARED_IN + sorted((ROOT / "Tests").rglob("*.lean"))

# Only `structure` declarations are scanned. `class` fields and inductive
# constructor parameters are not, so an allowlist entry naming one of those records
# a judgement about something this tool could never report. Three such entries were
# removed; that removal was **partial**, and review said so: eight entries below
# (`combine`, `alternative`, `zero`, `le`, `laws`, `limit`, `exhaustion`,
# `lifecycle`) name fields that appear on the `HasResourceAxis`/`HasResourceLimit`
# *classes* as well as on the `ResourceLimit` structure, so each is doing work for
# the structure and none for the class. `Grass/Resource/Algebra.lean`'s
# `ResourceModel.algebra` is a live instance of this tool's own defect class that it
# cannot see for the same reason.
#
# Extending the scan to classes would be a real change, not a regex tweak, because a
# class field is consumed through instance resolution that a text scan cannot see.
# `[A-Za-z]`, not `[a-z]`: a capital-initial field is a field. `ResourceLimit.Value`
# and `HasResourceAxis.Value` were outside the scan entirely, and both are live
# structure fields with no projection anywhere -- exactly what this tool reports,
# missed by a character class. Review found it.
DECL = re.compile(r"^\s{2,}(?:private\s+)?([A-Za-z][A-Za-z0-9_']*)\s*:\s*[^=]")
STRUCTURE = re.compile(r"^\s*(?:private\s+)?structure\s+([A-Za-z_][A-Za-z0-9_.']*)")

# Fields deliberately carried without a reader. Every entry states why, and the
# entry is the record that the decision was made.
#
# An entry may name a bare field (`label`) or a qualified one (`Structure.field`).
# Qualified is the better shape and the bare form survives for the entries whose
# reason really is about the name: a bare entry is a claim about every structure that
# will ever declare a field so called, which is the same overreach as a pattern.
#
# There *was* a pattern here, `PROOF_BUNDLES`, exempting any structure whose name
# ended in `Recognized` or `Laws` on the reason that a structure whose fields are
# propositions bundles proof obligations, so nothing projects them. It was written
# after `MemoryEvent.WellFormed` disproved the same reason for `WellFormed`: eleven of
# its thirteen clauses were projected nowhere and each could be replaced by `True`
# with the tree green, so "the constructor discharged it" is not "the obligation has
# content". The two survivors were kept as "whose fields really are
# discharged-and-done" and never measured.
#
# Review measured them. `Laws` matched exactly one structure and silenced seventeen of
# its twenty fields -- the same seventeen §4.4.1 records as never used by anything --
# and `Recognized` silenced one. So 94% of the pattern's work was on
# `Grass/Resource/Algebra.lean`, the module §4.4.1 calls the corner nobody reviews,
# and it was invisible twice over: `--inert` sweeps `ALLOWED` entries, so the check
# added "so the same rot is visible without a reviewer" could not see the mechanism
# that caused it, and §4.4.1's list of this tool's blind spots named two others and
# not this. The eighteen fields are individual entries below, `--inert` covers them
# like every other entry, and this tool now has one exemption mechanism rather than
# two.
#
# `AccessDescriptor.WellFormedIn` was never in scope for the pattern --
# `endswith("WellFormed")` does not match it -- which is the only reason the seal
# round eighteen swept was ever reported.

# Sixteen entries were deleted from this list after review checked, one at a time,
# whether removing an entry changed the report. It changed nothing for any of them.
# Two whole groups had reasons that were simply false: "diagnostic identity, never
# dispatched on" for `id` and `name`, which are projected twenty-nine and three times
# respectively, and "structural payloads consumed by pattern matching, which this tool
# cannot see" for `recognized`, `entries`, `runs`, `bytes`, `start`, `aliases` and
# `substeps`, every one of which is projected by name -- `d.range.start` alone appears
# a hundred and fifty times. The rest (`combine`, `alternative`, `le`, `laws`,
# `issuer`, `owner`, `restartability`) were suppressing nothing either, three of them
# because a field of the same name is projected on an unrelated structure, which is
# this tool's documented blind spot rather than a reason to exempt anything.
#
# An allowlist is a record of decisions. An entry that suppresses nothing records a
# decision about nothing, and a *false* reason attached to one is worse than silence:
# it reads as an argument someone checked. `--inert` reports them now, so the same
# rot is visible without a reviewer.
#
# `AddressSpace.owner` and `AccessDescriptor.restartability` are still genuine gaps
# with no reader; they are recorded in section 4.2 of
# docs/MEMORY_IMPLEMENTATION_PLAN.md and in their own docstrings, which is where a
# gap this tool cannot see belongs.
ALLOWED = {
    # Diagnostic identity: carried so a report or rejection can name which one,
    # never dispatched on. `id` and `name` were here too and suppressed nothing.
    "label",
    "origin",
    # --- The eighteen that `PROOF_BUNDLES` used to cover. Qualified, because the
    # --- reason is about these structures and not about anything named `evidence`.
    #
    # `Recognized.evidence` holds the proof that a name was admitted by the profile's
    # vocabulary. The elaborator reads it at construction, which is the whole point of
    # requiring it, and no later rule re-derives what the constructor already had to
    # supply.
    "Recognized.evidence",
    #
    # The seventeen laws of `OrderedPartialCommutativeResourceLaws`. §4.4.1 records
    # them as a gap and it is a real one: nothing under `Grass/` imports that module,
    # so the laws are stated and no theorem yet reasons through them. M7 is the
    # milestone that owes the consumers. They are listed here one by one rather than
    # covered by a suffix so that a reviewer reading the allowlist sees seventeen
    # decisions, which is what they are, and so that `--inert` reports each the day a
    # consumer arrives.
    "OrderedPartialCommutativeResourceLaws.compatibleComm",
    "OrderedPartialCommutativeResourceLaws.compatibleZero",
    "OrderedPartialCommutativeResourceLaws.combineComm",
    "OrderedPartialCommutativeResourceLaws.combineAssoc",
    "OrderedPartialCommutativeResourceLaws.combineZero",
    "OrderedPartialCommutativeResourceLaws.leRefl",
    "OrderedPartialCommutativeResourceLaws.leTrans",
    "OrderedPartialCommutativeResourceLaws.leAntisymm",
    "OrderedPartialCommutativeResourceLaws.zeroLe",
    "OrderedPartialCommutativeResourceLaws.leCombine",
    "OrderedPartialCommutativeResourceLaws.combineMonotone",
    "OrderedPartialCommutativeResourceLaws.combineEqLeft",
    "OrderedPartialCommutativeResourceLaws.alternativeComm",
    "OrderedPartialCommutativeResourceLaws.alternativeAssoc",
    "OrderedPartialCommutativeResourceLaws.alternativeZero",
    "OrderedPartialCommutativeResourceLaws.leAlternative",
    "OrderedPartialCommutativeResourceLaws.alternativeMonotone",
    # --- Carried without a projection. Being listed here is not "this is fine":
    # --- it is the record that someone read the corpus and decided. The reasons
    # --- differ, and conflating them is how the first version of section 4.2 of
    # --- docs/MEMORY_IMPLEMENTATION_PLAN.md called four milestone boundaries
    # --- defects.
    #
    # Genuine gaps: a corpus requirement, no consumer, and no milestone that owns
    # them. Recorded as owed in section 4.2.
    "observations",       # section 7.5 device observation labels; no reader at all
    "vocabularyVersion",  # one version exists, so nothing to compare against yet
    #
    # Not gaps: the consumer is a later milestone or another layer, and the field
    # is carried exactly as its own document requires.
    "memoryType",         # section 7.1 requires the event to carry it, and it does
    "coherence",          # likewise; the rules are section 7.2's, which is M8
    "package",            # section 10 gates VerifiedProgram, not this transition
    "obligation",         # TerminalOutcome awaits terminal accounting
    "disposition",   # TerminalOutcome, likewise
    # Proof obligations: their purpose is that a constructor had to discharge
    # them, so nothing projects them. The structure-suffix rule above misses these
    # because they sit on structures with other names.
    "readsFull",
    "writesFull",
    "vocabularyWellFormed",
    # Section 10 items that have stopped being `Prop`s the profile names. Their
    # fields hold *proofs* of propositions this layer states, so the elaborator
    # reads them at construction and nothing projects them afterwards -- that is
    # the whole point, and it is the opposite of a fact carried and never read.
    # `RequiredProofPackage.Holds` conjoins only the items still named, so each
    # one that gains a statement lands here.
    #
    # `RequiredProofPackage.loanMapLaws` belongs here on the same reasoning and is
    # NOT listed, because listing it would be an inert entry: the theorem
    # `MemoryState.loanMapLaws` shares its final name component, so the scan finds
    # a "projection" that is nothing of the kind and the field passes by accident.
    # That is this tool's documented same-name blind spot, recorded here rather
    # than papered over with an allowlist entry `--inert` would then report.
    "allocatorFreshnessTeardownEpoch",
    "rangeProvenanceInitializationPreservation",
    # The third of them, and it was invisible until the projection pattern stopped
    # counting a construction. The theorem discharging it is named after the field,
    # so `loanMapLaws := MemoryState.loanMapLaws` carried `.loanMapLaws` on its
    # right-hand side and the scan read that as a reader. Its two siblings, whose
    # theorems are named differently, were reported from the day they landed.
    "loanMapLaws",
    # --- Seals nothing requires, which is a different thing from a seal nothing
    # --- projects. Recorded rather than exempted by structure: dropping the
    # --- `WellFormed` structure exemption is what surfaced `MemoryEvent.WellFormed`'s
    # --- thirteen unswept clauses, and these two should not be hidden by the same
    # --- shape.
    #
    # `Footprint.WellFormed`'s own docstring says neither is load-bearing and that
    # the padding theorem "deliberately does not require `WellFormed` at all", so
    # unlike the event seal there is no consumer to disappoint. It is a seal a caller
    # may demand and none does.
    "namesUnique",
    "fieldsContained",
    # `ProtocolAuthority.issuer` records which profile minted authority so that a §10
    # package has something to check. `mintedBy` is the one door and no rule yet says
    # which profile may mint for which protocol; the field is the claim, and M10's
    # profile closure is the reader. Its own docstring says so.
    "issuer",
    # --- `Grass/Semantics/Execution.lean` is another owner's module, arrived by
    # --- merging main. Five fields of `InfiniteContinuation` and `ExecutionPrefix`
    # --- are unprojected there. Listed rather than silently skipped, and reported to
    # --- that owner rather than decided here: whether an infinite continuation's
    # --- witness fields are meant to be read is their call, not this layer's.
    "eventAt",
    "stateZero",
    "graphZero",
    "consistent",
    "initialGraph",
    # Diagnostic provenance carried into the trace for a report to read, never
    # dispatched on, like `id` and `origin` above.
    "cause",
    "substep",
    # The resource layer is built ahead of its consumers, which arrive at M7 and
    # M9. Nothing outside Grass/Resource projects any of it yet.
    # A field whose *type* is the point: every other field of `ResourceLimit` is
    # typed by it, so it is consumed by the structure's own signature and cannot be
    # "projected" in the sense this tool looks for. Found by widening the field
    # pattern to accept a capital initial, which is what made it visible at all.
    "Value",
    "zero",
    "limit",
    "exhaustion",
    "lifecycle",

    # Proof obligations on structures a *provider* supplies, from modules this
    # branch does not own -- Grass/Core/Demand.lean and Grass/Certificate.lean,
    # which arrived here by merging main. They do work unprojected, because a
    # provider cannot construct the structure without discharging them, which is
    # the same reason `readsFull` and `vocabularyWellFormed` are above. Listed
    # rather than silenced: this audit is the memory branch's, the modules are
    # another owner's, and whether anything downstream *uses* exactness or
    # injectivity is that owner's question, reported to them and not decided here.
    "complete",
    "unique",
    "identityInjective",
    "parseExact",
}

BLOCK = re.compile(r"/-.*?-/", re.DOTALL)
LINE = re.compile(r"--.*?$", re.MULTILINE)
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


def scannable(text: str) -> str:
    """Strip block comments, line comments, and string literals.

    Prose mentioning `.owner` and a docstring quoting a field name are not
    readers, and counting them was a false negative review found.
    """
    return STRING.sub('""', LINE.sub("", BLOCK.sub(" ", text)))


def fields_in(text: str) -> list[tuple[str, str, int]]:
    """Yield (structure, field, line) for every structure field in one source.

    A structure runs until `deriving` or until a line at column zero that is not
    blank. Field docstrings are skipped rather than treated as the end -- an
    earlier version ended the structure at the first `/--`, which meant it saw
    almost no fields and reported a clean tree. It was caught by probing it
    against a field already known to have no reader, which is the only way to
    tell a working audit from a silent one.
    """
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
        match = STRUCTURE.match(line)
        if match:
            current = match.group(1)
            continue
        if current is None:
            continue
        if stripped.startswith("deriving") or (stripped and not line.startswith(" ")):
            current = None
            continue
        declaration = DECL.match(line)
        if declaration:
            out.append((current, declaration.group(1), number))
    return out


def analyse(raw: dict[str, str],
            readers: dict[str, str] | None = None) -> list[str]:
    """Report `path:line: Structure.field` for every field name never projected.

    Takes the sources as text so the self-test can seed them. Only a projection
    counts: `name := value` is construction, which is a write, and counting it let
    an external constructor make an unread field pass.
    """
    corpus = {name: scannable(text) for name, text in (readers or raw).items()}
    unread: list[str] = []
    for name, text in raw.items():
        for structure, field, line in fields_in(text):
            if field in ALLOWED or f"{structure}.{field}" in ALLOWED:
                continue
            # A projection, on a line that does not also *construct* this field.
            # `RequiredProofPackage.loanMapLaws` escaped the report because the
            # theorem discharging it was named after it, so
            # `loanMapLaws := MemoryState.loanMapLaws` carries `.loanMapLaws` on its
            # right-hand side and the scan counted it. Its two sibling package
            # fields, whose theorems are named differently, were reported and
            # allowlisted. An eponymous discharge is not a reader.
            projection = re.compile(r"\.%s\b" % re.escape(field))
            construction = re.compile(r"\b%s\s*:=" % re.escape(field))
            def reads(body: str) -> bool:
                return any(projection.search(line) and not construction.search(line)
                           for line in body.splitlines())
            if not any(reads(body) for body in corpus.values()):
                unread.append(
                    f"  {name}:{line}: {structure}.{field} is declared and "
                    "its name is never projected"
                )
    return unread


def self_test() -> int:
    """Seed each false-negative class this file claims to have closed.

    A silent audit is worse than no audit, and the first version of this file was
    silent -- it treated a field docstring as the end of a structure, saw almost
    nothing, and reported a clean tree. These cases fail loudly if the scanner
    stops discriminating.
    """
    decl = 'structure Probe where\n  /-- doc -/\n  quarry : Nat\n'
    cases = [
        ("bare declaration", {"a.lean": decl}, True),
        ("real projection", {"a.lean": decl, "b.lean": "def f (p : Probe) := p.quarry\n"}, False),
        # Multi-line and not beginning with `--`, so the line-comment rule cannot
        # strip it. The single-line `/-- ... -/` case this replaced *began* with
        # `--`, so LINE stripped it and the case passed with BLOCK deleted
        # outright -- a self-test that could not fail for the thing it named.
        # Every module comment under Grass/ is exactly this shape.
        ("block comment mentioning .quarry",
         {"a.lean": decl,
          "b.lean": "/-!\nA module comment about .quarry\nspanning lines.\n-/\ndef f := 1\n"},
         True),
        ("line comment mentioning .quarry",
         {"a.lean": decl, "b.lean": "-- reads .quarry eventually\ndef f := 1\n"}, True),
        ("string literal mentioning .quarry",
         {"a.lean": decl, "b.lean": 'def f := "look at .quarry"\n'}, True),
        ("construction only",
         {"a.lean": decl, "b.lean": "def p : Probe := { quarry := 3 }\n"}, True),
    ]
    # The reader corpus is a separate parameter and no case above exercises it:
    # each passes one dict, so `main` dropping the Tests/ readers would go
    # unnoticed -- which the file's own comment calls out as a fixed false
    # positive.
    reader_cases = [
        ("reader only in the reader corpus",
         {"a.lean": decl},
         {"a.lean": decl, "t.lean": "def f (p : Probe) := p.quarry\n"}, False),
        ("no reader in either corpus",
         {"a.lean": decl}, {"a.lean": decl}, True),
    ]
    # An allowlist entry may be qualified, and both halves of that need a case: a
    # qualified entry must silence its own structure's field, and must not silence a
    # field of the same name on another structure -- which is the whole reason the
    # eighteen entries that replaced `PROOF_BUNDLES` are written qualified.
    other = 'structure Decoy where\n  quarry : Nat\n'
    global ALLOWED
    original = set(ALLOWED)
    try:
        ALLOWED = original | {"Probe.quarry"}
        if any("Probe.quarry" in line for line in analyse({"a.lean": decl})):
            print("  SELF-TEST FAILED: a qualified allowlist entry does not silence "
                  "its own field")
            failures_qualified = 1
        else:
            failures_qualified = 0
        if not any("Decoy.quarry" in line for line in analyse({"a.lean": other})):
            print("  SELF-TEST FAILED: a qualified allowlist entry silences the same "
                  "field name on another structure")
            failures_qualified += 1
    finally:
        ALLOWED = original

    failures = failures_qualified
    for label, sources, should_report in cases:
        reported = any("Probe.quarry" in line for line in analyse(sources))
        if reported != should_report:
            want = "reported" if should_report else "not reported"
            print(f"  SELF-TEST FAILED [{label}]: expected {want}")
            failures += 1

    for label, declared, readers, should_report in reader_cases:
        reported = any("Probe.quarry" in line for line in analyse(declared, readers))
        if reported != should_report:
            want = "reported" if should_report else "not reported"
            print(f"  SELF-TEST FAILED [{label}]: expected {want}")
            failures += 1

    # Documented blind spot, asserted so it cannot quietly become a silent pass
    # that someone mistakes for coverage. Distinguishing these needs elaboration.
    other = ('structure Probe where\n  /-- doc -/\n  quarry : Nat\n\n'
             'structure Decoy where\n  /-- doc -/\n  quarry : Nat\n')
    missed = not any("Probe.quarry" in line
                     for line in analyse({"a.lean": other,
                                          "b.lean": "def f (d : Decoy) := d.quarry\n"}))
    if not missed:
        print("  SELF-TEST FAILED [same-named field]: blind spot has changed; "
              "update the module docstring, which documents it as unhandled")
        failures += 1

    if failures:
        print(f"consulted audit self-test: {failures} failure(s)")
        return 1
    print("consulted audit self-test: all cases discriminate as documented")
    return 0


def inert_entries(declared: dict[str, str], readers: dict[str, str]) -> list[str]:
    """The `ALLOWED` entries whose removal would change nothing.

    An allowlist is a record of decisions, so an entry that suppresses nothing
    records a decision about nothing -- and a false *reason* attached to one is worse
    than silence, because it reads as an argument someone checked. Review found
    sixteen such entries here, two whole groups of them with reasons that were simply
    false. This is that check, mechanised.

    Reported rather than failed: an entry becomes inert when someone adds a
    projection, which is good news and should not break a build.
    """
    global ALLOWED
    original = set(ALLOWED)
    base = set(analyse(declared, readers))
    inert = []
    for entry in sorted(original):
        ALLOWED = original - {entry}
        if not set(analyse(declared, readers)) - base:
            inert.append(entry)
    ALLOWED = original
    return inert


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    declared = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                for path in DECLARED_IN}
    readers = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
               for path in READERS_IN}
    if "--inert" in sys.argv:
        inert = inert_entries(declared, readers)
        if inert:
            print("allowlist entries that suppress nothing: " + ", ".join(inert))
            print("Delete them, or say why the entry is kept with no effect.")
        else:
            print("consulted audit: every allowlist entry suppresses a report")
        return 0
    unread = analyse(declared, readers)

    if unread:
        print("\n".join(sorted(unread)))
        print("consulted audit: declared facts with no reader\n")
        print(
            f"{len(unread)} unread field(s). Either consult the field, delete it, "
            "or add it to ALLOWED with the reason it is carried."
        )
        return 1
    print(
        "consulted audit: no declared field name is entirely unprojected "
        "(a lexical check; see the module docstring for what it does not cover)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
