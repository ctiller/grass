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
# **The type may begin on the next line.** This required a non-`=` character after
# the colon *on the same line*, so a field whose proposition wraps -- which is what a
# long clause naturally does -- was not a field to this tool at all: not reported, not
# allowlistable, and invisible to `inert_entries` and `overbroad_entries`, which read
# the same `fields_in`. Five in-scope fields are written that way, two of them clauses
# of the event seal, so dropping the `WellFormed` structure exemption put nine of its
# eleven clauses in scope and the commit said eleven. `Tools/CitationAudit.py`'s
# `FIELD` already used the lookahead form. Widening it brought six fields into scope
# and produced no new report, because all six are projected -- which is why the gap
# was invisible.
# **And one space is indentation.** `^\s{2,}` was the next form of the same gap: a
# field indented by a single space is valid Lean and was not a field to this tool.
# The two-space floor was doing nothing `STRUCTURE.match` and `fields_in`'s
# unindented-line terminator do not already do. Latent when review found it -- no
# field under `Grass/` is written that way -- which is what a blind spot looks like
# from inside, and is the second round running that this pattern has been one
# character too strict.
DECL = re.compile(r"^\s+(?:private\s+)?([A-Za-z][A-Za-z0-9_']*)\s*:(?!=)")
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
    # Qualified after review measured it. Bare, this entry also silenced
    # `DerivedDemandFamily.origin` in `Grass/Core/Demand.lean` -- which is not
    # diagnostic identity at all: it is the field saying every demand in a derived
    # family either descends from a prior key *with a membership proof* or names an
    # external authority. It is another owner's module, of the kind the group below
    # says must be listed and reported rather than silenced, and it was silenced by an
    # entry from this group whose stated reason is about something else entirely.
    "EventCause.origin",
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
    # And `Grass/Core/Demand.lean`, the same way and for the same reason. This one was
    # *already* silenced, by the bare `origin` entry two groups above, whose reason
    # ("diagnostic identity, never dispatched on") is false of it. Reported to that
    # owner in `c-mem:53`, an addendum to `c-mem:52`, rather than decided here.
    "DerivedDemandFamily.origin",
    # Diagnostic provenance carried into the trace for a report to read, never
    # dispatched on, like `id` and `origin` above. Two structures carry a field so
    # named and the reason is true of both, so both are listed -- which is the point of
    # qualifying rather than the cost of it: the reason is now attached to a decision
    # about each, and a third `cause` arriving somewhere else will be reported.
    "MemoryEvent.cause",
    "RaisedFault.cause",
    "substep",
    # The resource layer is built ahead of its consumers, which arrive at M7 and
    # M9. Nothing outside Grass/Resource projects any of it yet.
    # A field whose *type* is the point: every other field of `ResourceLimit` is
    # typed by it, so it is consumed by the structure's own signature and cannot be
    # "projected" in the sense this tool looks for. Found by widening the field
    # pattern to accept a capital initial, which is what made it visible at all.
    "Value",
    "ResourceAlgebra.zero",
    "ResourceLimit.zero",
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
        # A field whose type begins on the next line. The pattern required a non-`=`
        # character after the colon on the same line, so a wrapped clause proposition
        # was not a field at all -- silent in both directions, since an unread one was
        # never reported and a read one was never counted.
        ("field whose type is on the next line",
         {"a.lean": "structure Probe where" + chr(10) + "  quarry :" + chr(10)
                    + "    Nat" + chr(10)}, True),
        # One space is indentation too. Latent when review seeded it, which is why the
        # case is here rather than in the tree.
        ("field indented by one space",
         {"a.lean": "structure Probe where" + chr(10) + " quarry : Nat" + chr(10)}, True),
        # And a `:=` default is still not a field declaration, which is what the
        # non-`=` requirement was there for.
        ("a default value is not a declaration",
         {"a.lean": "structure Probe where" + chr(10) + "  quarry := 3" + chr(10)}, False),
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

    # The over-broad check, both directions. A bare entry naming a field that two
    # structures declare is reported; the same entry qualified is not, and a bare entry
    # naming a field only one structure declares is not.
    two = ('structure Probe where\n  quarry : Nat\n'
           'structure Decoy where\n  quarry : Nat\n'
           'structure Only where\n  lone : Nat\n')
    try:
        ALLOWED = {"quarry"}
        if not overbroad_entries({"a.lean": two}):
            print("  SELF-TEST FAILED: a bare entry naming two structures' fields is "
                  "not reported as over-broad")
            failures_qualified += 1
        ALLOWED = {"Probe.quarry", "Decoy.quarry", "lone"}
        if overbroad_entries({"a.lean": two}):
            print("  SELF-TEST FAILED: qualified entries, or a bare entry with one "
                  "carrier, are reported as over-broad")
            failures_qualified += 1
    finally:
        ALLOWED = original

    # The seal-label check, both directions. An exchange is what review got through
    # three consistency theorems, so the exchanged case is the one that matters.
    seal_decl = ("structure WellFormed where" + chr(10)
                 + "  alpha : Nat" + chr(10) + "  beta : Nat" + chr(10))
    good = ("def sealClauses (e : E) : List String :=" + chr(10)
            + '  (if p then [] else ["alpha"]) ++' + chr(10)
            + '  (if q then [] else ["beta"])' + chr(10) + chr(10) + "/-! rest -/" + chr(10))
    swapped = good.replace('["alpha"]', '["ZZ"]').replace('["beta"]', '["alpha"]') \
                  .replace('["ZZ"]', '["beta"]')
    if seal_labels(seal_decl, good):
        print("  SELF-TEST FAILED: labels matching the field names are reported")
        failures_qualified += 1
    if not seal_labels(seal_decl, swapped):
        print("  SELF-TEST FAILED: two exchanged labels are not reported")
        failures_qualified += 1
    if not seal_labels(seal_decl, "def nothingLikeIt := 1" + chr(10)):
        print("  SELF-TEST FAILED: a missing `sealClauses` is not reported")
        failures_qualified += 1

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


# The seal's label list, and the structure whose field names it must reproduce.
#
# `Tests/Memory/EventClauses.lean`'s `sealClauses` returns the names of the clauses an
# event fails. Three theorems in that file tie those strings to propositions, to
# neighbours, and to `MemoryEvent.WellFormed` itself -- and none of them ties a string
# to a *field name*, because nothing inside Lean can without metaprogramming. Review
# exchanged two labels across all three sites and every gate stayed green, leaving the
# file attesting that the neighbour whose status disagrees about reads is caught by the
# clause called `statusAgreesWithWrites`. Each consistency check raised the price of a
# mislabelling by one edit; none of them anchored it.
#
# **This check lives here for the parser and not for the subject.** Its subject is a
# fixture file agreeing with a structure, which is nobody's gate; this is the tool that
# already reads `structure` fields in declaration order, and inventing an eighth gate for
# one check would be worse. Order is the available anchor because
# `sealClauses_is_the_seal`'s proof consumes the fields positionally, so position is
# already pinned to the structure and only the names ride free.
SEAL_STRUCTURE = ("Grass/Memory/Event.lean", "WellFormed")
SEAL_LABELS = ("Tests/Memory/EventClauses.lean", "def sealClauses")
SEAL_LABEL = re.compile(
    r"else " + chr(92) + r"[" + chr(34) + r"([A-Za-z][A-Za-z0-9_']*)" + chr(34)
    + chr(92) + r"]")


def seal_labels(structure_text: str, labels_text: str) -> list[str]:
    """Report the seal's labels where they do not reproduce its field names, in order.

    Lexical, like everything else here. The label list is read from the body of
    `sealClauses` alone -- up to the first blank line -- because the same string literals
    appear again in the theorems below it, and a check that read those too would compare
    a list against itself.
    """
    fields = [field for structure, field, _ in fields_in(structure_text)
              if structure == SEAL_STRUCTURE[1]]
    start = labels_text.find(SEAL_LABELS[1])
    if start < 0:
        return [f"  {SEAL_LABELS[0]}: `{SEAL_LABELS[1]}` is gone, so the seal's labels "
                "are no longer checked against its field names"]
    body = labels_text[start:]
    end = body.find(chr(10) * 2)
    labels = SEAL_LABEL.findall(body if end < 0 else body[:end])
    if labels == fields:
        return []
    return [f"  {SEAL_LABELS[0]}: `sealClauses` emits {labels}, and "
            f"`{SEAL_STRUCTURE[1]}` declares {fields}, in that order"]


def overbroad_entries(declared: dict[str, str]) -> list[str]:
    """Report every bare `ALLOWED` entry that names a field on more than one structure.

    An entry may be written bare (`label`) or qualified (`Structure.field`). A bare
    entry exempts its name *everywhere*, so it can be a true statement about one
    structure and a silent one about another -- and `inert_entries` cannot say so,
    because leave-one-out asks whether an entry suppresses something and never how
    much.

    Review found three. The one that mattered was `origin`: written for
    `EventCause.origin` under the reason "diagnostic identity, never dispatched on",
    it also silenced `DerivedDemandFamily.origin` in another owner's module -- a field
    carrying the proof that a derived demand descends from a prior key, in the very
    module this file's own comments say must be *listed and reported* rather than
    silenced.

    This is round twenty's lesson one level in. That round replaced a structure-name
    *pattern* with per-field entries because "an exemption keyed on a name pattern is a
    claim about every structure that will ever match it". A bare entry is a name
    pattern with one element. Failing rather than reporting, because unlike an inert
    entry this does not become true on its own: it is a claim nobody made, and the fix
    is always the same one line.
    """
    owners: dict[str, set[str]] = {}
    for text in declared.values():
        for structure, field, _ in fields_in(text):
            owners.setdefault(field, set()).add(structure)
    out = []
    for entry in sorted(ALLOWED):
        if "." in entry:
            continue
        carriers = sorted(owners.get(entry, ()))
        if len(carriers) > 1:
            out.append(
                f"  ALLOWED entry {entry!r} names a field on "
                + str(len(carriers))
                + " structures: "
                + ", ".join(f"{c}.{entry}" for c in carriers)
            )
    return out


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
    mislabelled = seal_labels(
        declared.get(SEAL_STRUCTURE[0], ""),
        (ROOT / SEAL_LABELS[0]).read_text(encoding="utf-8"))
    if mislabelled:
        print("\n".join(mislabelled))
        print("\nconsulted audit: the seal's labels do not name its clauses\n")
        print(
            "Read the two lists against each other. `sealClauses` reproduces "
            "`MemoryEvent.WellFormed`'s field names in declaration order, and nothing "
            "inside Lean can say so."
        )
        return 1
    overbroad = overbroad_entries(declared)
    if overbroad:
        print("\n".join(overbroad))
        print("\nconsulted audit: an allowlist entry claims more than one structure\n")
        print(
            f"{len(overbroad)} bare entry/entries. Qualify each as `Structure.field` "
            "for the structures the reason is actually about."
        )
        return 1
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
