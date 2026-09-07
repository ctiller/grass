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
- It cannot tell a projection from a suffix that merely looks like one.
- Comments and string literals are stripped before scanning, so prose mentioning
  `.owner` no longer counts as a reader. That was a real false negative.
- A construction `name := value` is a write, not a read, and is not counted. That
  was also a real false negative: an external constructor made an unread field
  pass.

So a clean run means **no field name declared in `SCOPE` is entirely absent from the
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


DECLARED_IN = [p for p in sorted((ROOT / "Grass").rglob("*.lean")) if in_scope(p)]
# Readers are looked for in the fixtures too: a field a fixture projects is read,
# and excluding them made AuditViolation.class_ look inert when Tests/ reads it.
#
# **Unscoped, both trees.** This was `DECLARED_IN + Tests/`, which scopes the
# `Grass/` half to `SCOPE` and leaves the `Tests/` half whole -- so a field read
# only from `Grass/ISA` was reported unread while one read only from `Tests/ISA`
# was not. Same owner, same out-of-scope status, opposite verdict; review built
# one probe and moved its single consumer between three files to isolate it.
#
# A declaration is *used* wherever it is used. Only the set this gate
# **adjudicates** belongs in `SCOPE`, which is the distinction `CitationAudit`
# was given a round earlier and `FixtureAudit` already had. Applying it to one
# gate of three was the repair landing on the instance instead of the class.
# It also silently corrupted `--inert`, which reads the same narrowed window.
READERS_IN = (sorted((ROOT / "Grass").rglob("*.lean"))
              + sorted((ROOT / "Tests").rglob("*.lean")))

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
    # --- g-foundation's, and reported the first time this gate scanned the file:
    # --- main changed `Grass/Verify/VerifiedProgram.lean` in the merge at 3c2b7e9
    # --- and this gate is not on main. `CompletionRefinement.loaded` is declared
    # --- and never projected; its sibling `portable` is. Every other `.loaded` in
    # --- the tree is `loadedBehavior` or `loadedAdequate`, which are other names,
    # --- so same-name blindness is not what is quieting it.
    # ---
    # --- Routed to g-foundation as `c-mem:57`, which asks whether the pairing of
    # --- the two completions is itself the content. This entry is a placeholder
    # --- for that answer and not a judgement c-mem is entitled to make about
    # --- another owner's structure; when the answer lands, this reason is replaced
    # --- by it or the entry goes.
    "CompletionRefinement.loaded",
    # --- Six entries left this list on merging `origin/main`, and they left for
    # --- three different reasons, which the note that deleted them gave as one.
    #
    # --- FOUR to same-name blindness: `label`, `observations`, `disposition` and
    # --- `lifecycle` stopped suppressing anything not because the memory-layer
    # --- field gained a reader, but because another tree now declares a field of
    # --- the same name and projects *it*. `AccessDescriptor.observations` still
    # --- has no reader; so does `PendingRender.observations`; one projection
    # --- satisfies the scan for both. That is the warning.
    #
    # --- ONE to a genuine reader: `ExecutionPrefix.initialGraph` gained one in the
    # --- merge, `ExecutionPrefix.ext` in its own declaring module. Good news,
    # --- reported as a warning, because the note counted causes by their number
    # --- rather than checking them one at a time.
    #
    # --- AND ONE THAT NEVER WENT INERT AT ALL. `parseExact` is declared once in
    # --- the whole tree and constructed once, and no other tree carries the name.
    # --- It stopped being reported because `Grass/Certificate.lean` fell out of
    # --- `SCOPE` -- a hand-written list that dropped three of this branch's own
    # --- pre-merge subtrees. Deleting the entry turned a recorded, routed gap into
    # --- one recorded nowhere and reportable nowhere. It is back, qualified, with
    # --- the reason the group above gives: another owner's module, listed rather
    # --- than silently skipped, and reported to them rather than decided here.
    #
    # --- **A cause read off a coincidence of timing is not a cause.** Six entries
    # --- went inert in one commit and the note attributed all six to the one
    # --- mechanism that explained the first it looked at.
    "ArtifactFormat.parseExact",
    #
    # --- **Merging main widened this scan's same-name blind spot materially.** It
    # --- was a documented limitation with a handful of instances; over a tree three
    # --- times the size it is the ordinary case for any short field name. The
    # --- entries are deleted because an entry that suppresses nothing records
    # --- nothing, and section 4.4.1 carries what they were covering, because this
    # --- gate can no longer say it.
    # Diagnostic identity: carried so a report or rejection can name which one,
    # never dispatched on. `id` and `name` were here too and suppressed nothing.
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
    "vocabularyVersion",  # one version exists, so nothing to compare against yet
    #
    # Not gaps: the consumer is a later milestone or another layer, and the field
    # is carried exactly as its own document requires.
    "memoryType",         # section 7.1 requires the event to carry it, and it does
    "coherence",          # likewise; the rules are section 7.2's, which is M8
    "package",            # section 10 gates VerifiedProgram, not this transition
    "obligation",         # TerminalOutcome awaits terminal accounting
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
    # --- merging main. This group held four fields of `InfiniteContinuation`, then
    # --- five with `ExecutionPrefix.initialGraph`; **one is left**.
    # ---
    # --- `eventAt`, `stateZero` and `graphZero` went inert in the merge at 3c2b7e9
    # --- and are deleted. They went for the *good* reason, which is worth
    # --- separating from the four that went to same-name blindness a merge earlier:
    # --- their declaring module grew genuine readers (`Grass/Semantics/Execution.lean`
    # --- lines 102 and 115-116), and `Grass/Certificate.lean` projects all three
    # --- when it maps a continuation through a refinement. The field became
    # --- consulted; that is the one way an entry in this group is supposed to end.
    # ---
    # --- `consistent` stays, and *not* because nothing names it. `Grass/Certificate
    # --- .lean:179` is `consistent := refinement.infiniteConsistency
    # --- execution.consistent` -- a projection on the very line that constructs the
    # --- field, which the rule three paragraphs down deliberately declines to count,
    # --- for the reason `RequiredProofPackage.loanMapLaws` taught: an eponymous
    # --- discharge is not a reader. Deleting this entry does report the field;
    # --- that was checked by removing it and running the gate, not by reading it.
    # --- Still another owner's call, routed with the rest as `c-mem:57`.
    "consistent",
    # And `Grass/Core/Demand.lean`, the same way and for the same reason. This one was
    # *already* silenced, by the bare `origin` entry two groups above, whose reason
    # ("diagnostic identity, never dispatched on") is false of it. Reported to that
    # owner in `c-mem:53`, an addendum to `c-mem:52`, rather than decided here.
    # --- And five more went inert one commit later, when `SCOPE` was corrected.
    # --- `InfiniteContinuation.stateAt`, `.graphAt`, `.choiceAt`, `SpecProcess.admits`
    # --- and `SpecProcess.observationProjection` are still declared and still
    # --- projected nowhere in their own modules. They read as inert because the
    # --- *declaration* side of this scan is scoped and the *reader* side is not, and
    # --- must not be: a field may legitimately be read from another owner's code, so
    # --- the corpus is the whole tree and a same-named projection anywhere satisfies
    # --- the scan. That asymmetry is correct and it is what makes the blindness
    # --- worse on a large tree than on a small one.
    #
    # --- They are recorded here rather than listed, on this branch's own rule: an
    # --- entry that suppresses nothing records a decision about nothing, and one
    # --- kept anyway reads as a judgement the gate is still making. `c-mem:55`
    # --- reported them to `Grass/Semantics`'s owner as allowlisted; the correction
    # --- is that they are reported and no longer allowlistable, which is a weaker
    # --- position and the true one.
    "DerivedDemandFamily.origin",
    # Five more of the same, which merging `origin/main` brought in: three witness
    # fields of `InfiniteContinuation` beside the four already listed, and both fields
    # of `SpecProcess`. Same reason and same routing -- listed rather than silently
    # skipped, reported to that owner rather than decided here. `SpecProcess.admits` is
    # the one worth their eye: a process specification whose admission relation nothing
    # projects is a specification nothing checks against.
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
}

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
APOSTROPHE = chr(39)
# Characters an apostrophe may follow as a *prime* on a name rather than opening a
# char literal. Lean allows `h'`, `foo''` and `x?'`.
PRIMEABLE = frozenset(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_!?" + chr(39))
BACKSLASH = chr(92)


def scannable(text: str) -> str:
    """Strip block comments, line comments, and string literals.

    Prose mentioning `.owner` and a docstring quoting a field name are not
    readers, and counting them was a false negative review found.
    """
    out: list[str] = []
    depth = 0
    in_string = False
    in_line_comment = False
    index = 0
    size = len(text)
    while index < size:
        char = text[index]
        if char == chr(10):
            out.append(chr(10))
            in_line_comment = False
            # A string left open at a newline is a lexical error in the source
            # rather than licence to blank the rest of the file. Reached only when
            # the newline is *not* part of a string gap; a gap is consumed by the
            # escape branch below, which keeps `in_string` set.
            in_string = False
            index += 1
            continue
        if in_line_comment:
            out.append(chr(32))
            index += 1
            continue
        if in_string:
            if char == BACKSLASH and index + 1 < size:
                # A **string gap**: a backslash immediately before a newline
                # continues the literal onto the next line. Lean 4 has these, and
                # the comment above this branch used to say it did not. Emitting
                # two spaces here consumed the newline: total length was preserved,
                # so the advertised invariant appeared to hold, while the line count
                # dropped and every finding after the gap was reported one line
                # early. Review measured it -- a door call on line 195 reported as
                # 194, with a gap-free control on 191 reported correctly.
                #
                # The newline is emitted and `in_string` stays set, because the
                # literal really does continue.
                # CRLF first, and it is the half that is unsafe rather than
                # merely wrong. On a CRLF checkout the escape ate the
                # backslash and the CR, the LF then hit the top-of-loop reset,
                # and `in_string` cleared **mid-string** -- so the
                # continuation line was scanned as source while the string's
                # own tail was not, which is the hiding direction. What holds
                # it off today is `.gitattributes` (`* text=auto eol=lf`),
                # which no gate consults, against a repo-local
                # `core.autocrlf=true`.
                if (index + 2 < size and text[index + 1] == chr(13)
                        and text[index + 2] == chr(10)):
                    out.append(chr(32))
                    out.append(chr(13))
                    out.append(chr(10))
                    index += 3
                    continue
                if text[index + 1] == chr(10):
                    out.append(chr(32))
                    out.append(chr(10))
                    index += 2
                    continue
                out.append(chr(32) * 2)
                index += 2
                continue
            out.append(chr(32))
            if char == QUOTE:
                in_string = False
            index += 1
            continue
        if depth > 0:
            if text.startswith(chr(47) + chr(45), index):
                depth += 1
                out.append(chr(32) * 2)
                index += 2
                continue
            if text.startswith(chr(45) + chr(47), index):
                depth -= 1
                out.append(chr(32) * 2)
                index += 2
                continue
            out.append(chr(32))
            index += 1
            continue
        if text.startswith(chr(47) + chr(45), index):
            depth = 1
            out.append(chr(32) * 2)
            index += 2
            continue
        if text.startswith(chr(45) * 2, index):
            in_line_comment = True
            out.append(chr(32) * 2)
            index += 2
            continue
        # A char literal, before the quote branch, because `'"'` holds a bare
        # quote and opened a string that blanked the rest of the line -- review put
        # two door calls on one line either side of one and watched the second
        # disappear. Only when the apostrophe cannot be a prime on an identifier:
        # `h'` and `foo'` are ordinary Lean names and must not start a literal.
        if char == APOSTROPHE and not (out and out[-1][-1:] in PRIMEABLE):
            if (index + 3 < size and text[index + 1] == BACKSLASH
                    and text[index + 3] == APOSTROPHE):
                out.append(chr(32) * 4)
                index += 4
                continue
            if index + 2 < size and text[index + 2] == APOSTROPHE:
                out.append(chr(32) * 3)
                index += 3
                continue
        if char == QUOTE:
            in_string = True
            out.append(chr(32))
            index += 1
            continue
        out.append(char)
        index += 1
    return "".join(out)


def fields_in(text: str) -> list[tuple[str, str, int]]:
    """Yield (structure, field, line) for every structure field in one source.

    A structure runs until `deriving` or until a line at column zero that is not
    blank. Field docstrings are skipped rather than treated as the end -- an
    earlier version ended the structure at the first `/--`, which meant it saw
    almost no fields and reported a clean tree. It was caught by probing it
    against a field already known to have no reader, which is the only way to
    tell a working audit from a silent one.

    **Comments are blanked before the walk rather than skipped during it.** The hand-
    rolled skipper this replaces discarded any line whose first token opened a comment,
    so a declaration sharing a line with its own docstring -- `/-- doc -/ | reclaimed`,
    which is legal Lean -- was not merely unreported but never examined. Review seeded
    an inductive written that way and an unread structure field written that way, and
    every gate stayed green. `BLOCK.sub(blank, ...)` leaves whatever follows the `-/`
    on the line and keeps the line number, which is what the walk needs and what the
    skipper could not give it.
    """
    out: list[tuple[str, str, int]] = []
    current: str | None = None
    for number, line in enumerate(scannable(text).splitlines(), 1):
        stripped = line.strip()
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
        # A field sharing a line with its own docstring. The hand-rolled comment
        # skipper discarded the whole line, so such a field was never examined -- which
        # is the documented historical failure of this function ("saw almost no fields
        # and reported a clean tree") in a narrower form nobody re-tested.
        ("field sharing a line with its docstring",
         {"a.lean": "structure Probe where" + chr(10)
                    + "  /-- doc -/ quarry : Nat" + chr(10)}, True),
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

    # `in_scope`, both directions, and the floor. `SCOPE` was a coverage claim with
    # nothing behind it: review dropped one token and this gate went silent for the
    # memory layer while still printing its success line. No self-test reached the
    # path filter, because every case here writes probes into a temporary directory
    # and calls the scanner directly.
    # **One case per `SCOPE` token.** This was `Memory` alone, and review measured
    # what that pinned: a leave-one-out over every token found 36 of 44 (gate,
    # token) pairs silent across the four scoped gates -- token deleted, self-test
    # green, gate green, success line printed. Seven were silent in all four,
    # `Obligation` among them, so dropping it took every `Grass/Obligation` file
    # out of every gate invisibly. That is the defect the plan records as closed,
    # reproduced against the subtree carrying `LedgerDelta.Applicable`.
    #
    # The floor cannot cover this and the docstring is right that it cannot: a
    # check derived from `SCOPE` is deleted along with the token. Only a
    # hard-coded name survives its removal, so there has to be one per token.
    if not in_scope(ROOT / "Grass" / "Certificate.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Certificate")
        failures_qualified += 1
    if not in_scope(ROOT / "Grass" / "Core" / "Context.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Core")
        failures_qualified += 1
    if not in_scope(ROOT / "Grass" / "Memory" / "State.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Memory")
        failures_qualified += 1
    if not in_scope(ROOT / "Grass" / "Obligation" / "Core.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Obligation")
        failures_qualified += 1
    if not in_scope(ROOT / "Grass" / "Op" / "Facets.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Op")
        failures_qualified += 1
    if not in_scope(ROOT / "Grass" / "Resource" / "Algebra.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Resource")
        failures_qualified += 1
    if not in_scope(ROOT / "Grass" / "Semantics" / "Execution.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Semantics")
        failures_qualified += 1
    if not in_scope(ROOT / "Grass" / "Std" / "Logical" / "Bag.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Std")
        failures_qualified += 1
    if not in_scope(ROOT / "Grass" / "Trust" / "Audit.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Trust")
        failures_qualified += 1
    if not in_scope(ROOT / "Grass" / "Verify" / "VerifiedProgram.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Verify")
        failures_qualified += 1
    if not in_scope(ROOT / "Tests" / "Foundation.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Foundation")
        failures_qualified += 1
    if not in_scope(ROOT / "Tests" / "Memory" / "Loans.lean"):
        print("  SELF-TEST FAILED: Tests/Memory is out of scope")
        failures_qualified += 1
    if in_scope(ROOT / "Grass" / "ISA" / "X86" / "Decode.lean"):
        print("  SELF-TEST FAILED: Grass/ISA is in scope")
        failures_qualified += 1
    if in_scope(ROOT / "Grass" / "Process" / "Bag.lean"):
        print("  SELF-TEST FAILED: Grass/Process is in scope")
        failures_qualified += 1
    if scope_is_covered(DECLARED_IN, ("Grass",)):
        print("  SELF-TEST FAILED: a SCOPE subtree on disk reached no file")
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

    # The shared scanner, both shapes review defeated it with. Neither had a
    # case here: `BACKSLASH` appeared only in this file's own comment, constant
    # and single use, and no seed contained an apostrophe -- so both defects were
    # invisible to CI while the gate printed its success line.
    #
    # A **string gap** -- a backslash immediately before a newline -- continues a
    # Lean literal. The escape branch used to consume the newline, preserving
    # total length while dropping a line, so every finding below a gap was
    # reported one line early. Length is the invariant the docstring advertises
    # and it is the weaker one; the line count is what a report cites.
    gapped = ("def s : String :=" + chr(10) + "  " + chr(34) + "a" + chr(92) + chr(10)
               + "  b" + chr(34) + chr(10) + "def afterGap := 1" + chr(10))
    if scannable(gapped).count(chr(10)) != gapped.count(chr(10)):
        print("  SELF-TEST FAILED: a string gap loses a line, shifting every "
              "reported line number after it")
        failures += 1

    # The same gap with **CRLF** endings, which is the half that hides source
    # rather than merely shifting a number. The escape ate the backslash and the
    # CR; the LF then hit the top-of-loop reset and cleared `in_string`
    # mid-literal, so the string's own tail was scanned as source. Held off only
    # by `.gitattributes`, which no gate consults.
    crlf = ("def s : String :=" + chr(13) + chr(10) + "  " + chr(34) + "a" + chr(92) + chr(13) + chr(10)
            + "  MemoryState.alias" + chr(34) + chr(13) + chr(10))
    if "MemoryState.alias" in scannable(crlf):
        print("  SELF-TEST FAILED: a CRLF string gap exposes the string's tail "
              "as source")
        failures += 1
    if scannable(crlf).count(chr(10)) != crlf.count(chr(10)):
        print("  SELF-TEST FAILED: a CRLF string gap loses a line")
        failures += 1

    # A **char literal** holding a quote must not open a string and blank the
    # rest of the line. Review put two door calls either side of one and watched
    # the second disappear.
    charlit = "def p := (alpha, " + chr(39) + chr(34) + chr(39) + ", omega)" + chr(10)
    if "omega" not in scannable(charlit):
        print("  SELF-TEST FAILED: a char literal holding a quote hides the "
              "rest of its line")
        failures += 1

    # Controls, so neither repair is a blanket disabling. A real string literal
    # is still blanked, and an apostrophe that is a *prime* on a name -- `h'`,
    # ordinary Lean -- does not start a literal and eat what follows.
    if "hidden" in scannable("def s := " + chr(34) + "hidden" + chr(34) + chr(10)):
        print("  SELF-TEST FAILED: a real string literal is no longer blanked")
        failures += 1
    if "visible" not in scannable("theorem h" + chr(39) + " : True := visible" + chr(10)):
        print("  SELF-TEST FAILED: a primed identifier swallows what follows it")
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
    # The scope floor, before anything else runs. `SCOPE` is a coverage claim and
    # review showed it was one nothing checked: dropping a single token from it
    # switched this gate off for the memory layer and it printed its success line.
    uncovered_scope = scope_is_covered(DECLARED_IN, ("Grass",))
    if uncovered_scope:
        print(chr(10).join(uncovered_scope))
        print(chr(10) + "SCOPE names a subtree that reached no file. Widen the"
              " globs or correct SCOPE -- a gate that scans nothing passes.")
        return 1
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
