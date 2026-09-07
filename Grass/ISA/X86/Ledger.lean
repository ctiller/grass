import Grass.ISA.X86.DualCitation

/-!
# The per-profile trust ledger

`docs/VALIDATION.md` §6 requires each ISA profile to publish, among other
things, "exact authoritative sources and revisions", "implemented and rejected
feature sets", and "known discrepancies, errata, and mitigations". This module
is the ledger that carries those, derived from the citation records themselves
rather than maintained beside them.

## Coverage is the load-bearing law

`docs/DECISIONS.md` 21 requires citations for *all* instruction and API
behavior, and `docs/INSTRUCTIONS.md` §1 says "Missing metadata is rejection, not
a default empty effect." `Ledger.Covers` and `Ledger.uncovered` are how a
profile discharges that: a profile states the declarations it models, and the
ledger either accounts for every one of them or names the ones it does not.

An accounted subject is *common*, *refined*, or *excluded*. Nothing is accounted
for by silence, which is the whole point — a subject absent from all three lists
is uncovered, and `uncovered` returns it.

## Coherence is not bookkeeping tidiness

The three lists must be disjoint, and this is a semantic requirement rather than
hygiene:

- A subject that is both common and excluded is a contradiction: the profile
  claims a guarantee for something it also claims not to model.
- A subject that is both refined and excluded is the same contradiction one
  vendor at a time.
- A duplicated common subject means two rules claim to be *the* intersection
  guarantee for one declaration, and a consumer reading the first would get a
  different answer than one reading the second.
- The same argument applies to two refinements *from one vendor* for one
  subject, which the first version of this predicate did not exclude: a reviewer
  built a ledger where Intel both set and cleared a flag and it was `Coherent`.
  Two refinements from *different* vendors for one subject are fine and
  expected, so the check is on the subject-and-vendor pair.

A refinement *may* share a subject with a common rule — that is exactly the
`supersedes` case, a vendor strengthening a common guarantee — so those two are
not disjoint, and `Coherent` does not pretend otherwise.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Cite

/--
A profile's published citation ledger.

The three lists are the three dispositions of `docs/INSTRUCTIONS.md` §7. There
is no fourth "documented elsewhere" list, because that is the escape hatch that
would make coverage unfalsifiable.
-/
structure Ledger where
  /-- The profile this ledger belongs to. -/
  profile : Name
  /-- Rules of the intersection, each dual-cited. -/
  common : List CommonRule
  /-- Single-vendor facts outside the intersection, each a `VendorRefinement`. -/
  refinements : List VendorRefinement
  /-- Constructs the profile does not model, each dual-cited. -/
  exclusions : List Excluded

namespace Ledger

/-- An empty ledger for a named profile. Covers nothing, which is correct. -/
def empty (profile : Name) : Ledger :=
  { profile := profile, common := [], refinements := [], exclusions := [] }

/-- Subjects with an intersection guarantee. -/
def commonSubjects (l : Ledger) : List Name := l.common.map (·.subject)

/-- Subjects with a single-vendor guarantee. -/
def refinedSubjects (l : Ledger) : List Name := l.refinements.map (·.subject)

/-- Subjects the profile declines to model. -/
def excludedSubjects (l : Ledger) : List Name := l.exclusions.map (·.subject)

/--
Whether the ledger accounts for a subject at all.

Note that "accounted for" includes `excluded`. A profile that has decided not to
model `PREFETCHW` has accounted for it; a profile that has never considered it
has not, and only the second is a coverage failure.
-/
def Accounts (l : Ledger) (subject : Name) : Prop :=
  subject ∈ l.commonSubjects ∨ subject ∈ l.refinedSubjects ∨
    subject ∈ l.excludedSubjects

instance (l : Ledger) (subject : Name) : Decidable (l.Accounts subject) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/--
The ledger accounts for every declaration the profile claims to model.

`modeled` is supplied by the profile, not derived from the ledger: deriving it
would let the ledger define its own obligation and always discharge it.
-/
def Covers (l : Ledger) (modeled : List Name) : Prop :=
  ∀ subject ∈ modeled, l.Accounts subject

instance (l : Ledger) (modeled : List Name) : Decidable (l.Covers modeled) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The modeled declarations this ledger fails to account for.

`Covers` says whether the profile is complete; this says what to go and cite. -/
def uncovered (l : Ledger) (modeled : List Name) : List Name :=
  modeled.filter (fun s => !decide (l.Accounts s))

theorem covers_iff_uncovered_nil (l : Ledger) (modeled : List Name) :
    l.Covers modeled ↔ l.uncovered modeled = [] := by
  constructor
  · intro h
    exact List.filter_eq_nil_iff.mpr fun s hs => by simp [h s hs]
  · intro h s hs
    simpa using List.filter_eq_nil_iff.mp h s hs

/--
The ledger's three dispositions do not contradict each other.

See this module's header for why each conjunct is semantic rather than
cosmetic. Refinement subjects are deliberately allowed to coincide with common
subjects: that is `VendorRefinement.supersedes`.
-/
def Coherent (l : Ledger) : Prop :=
  l.commonSubjects.Nodup ∧
    (l.refinements.map (fun r => (r.subject, r.vendor))).Nodup ∧
    l.excludedSubjects.Nodup ∧
    (∀ s ∈ l.excludedSubjects, s ∉ l.commonSubjects) ∧
    (∀ s ∈ l.excludedSubjects, s ∉ l.refinedSubjects)

instance (l : Ledger) : Decidable l.Coherent :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

@[simp] theorem coherent_empty (profile : Name) : (empty profile).Coherent := by
  refine ⟨List.nodup_nil, ?_, ?_⟩ <;> simp [empty, excludedSubjects]

/-- A ledger satisfying `Coherent` never both guarantees and declines one
subject. -/
theorem not_common_of_excluded {l : Ledger} (h : l.Coherent) {s : Name}
    (hs : s ∈ l.excludedSubjects) : s ∉ l.commonSubjects := h.2.2.2.1 s hs

/-- A coherent ledger never both refines and declines the same subject. -/
theorem not_refined_of_excluded {l : Ledger} (h : l.Coherent) {s : Name}
    (hs : s ∈ l.excludedSubjects) : s ∉ l.refinedSubjects := h.2.2.2.2 s hs

/--
Every citation this ledger rests on.

Both sides of every dual citation appear, which is the point: a report that
listed one anchor per rule would hide exactly the lopsidedness
`docs/DECISIONS.md` 15 is about.
-/
def citations (l : Ledger) : List Citation :=
  l.common.flatMap (fun r => r.citation.citations) ++
    l.refinements.map (·.citation) ++
    l.exclusions.flatMap (fun e => e.citation.citations)

/--
Every source document this ledger depends on, with duplicates.

Used for the "exact authoritative sources and revisions" line of
`docs/VALIDATION.md` §6 and as the input to a drift report. Deduplication is
left to the caller because the multiplicity is itself informative: it says how
many rules a revision bump would put back under review.
-/
def documents (l : Ledger) : List SourceDocument := l.citations.map (·.document)

/--
Anchors nobody has yet followed inside the document.

See `Grass.Cite.Citation.confirmed`. This is a work list, not a defect list: an
anchor written from working knowledge is a legitimate intermediate state, and
what `docs/VALIDATION.md` §1 forbids is leaving its status unrecorded.
-/
def unconfirmedAnchors (l : Ledger) : List Citation :=
  l.citations.filter (fun c => !c.isConfirmed)

/-- Every anchor in this ledger has been followed inside its document. -/
def AnchorsConfirmed (l : Ledger) : Prop :=
  ∀ c ∈ l.citations, c.isConfirmed = true

instance (l : Ledger) : Decidable l.AnchorsConfirmed :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

theorem anchorsConfirmed_iff_unconfirmed_nil (l : Ledger) :
    l.AnchorsConfirmed ↔ l.unconfirmedAnchors = [] := by
  constructor
  · intro h
    exact List.filter_eq_nil_iff.mpr fun c hc => by simp [h c hc]
  · intro h c hc
    simpa using List.filter_eq_nil_iff.mp h c hc

/--
Every citation is checkable end to end: live document, confirmed anchor.

This is the state a profile must reach before its citations mean what
`docs/DECISIONS.md` 21 says they mean.
-/
def CitationsChecked (l : Ledger) : Prop := ∀ c ∈ l.citations, c.FullyChecked

instance (l : Ledger) : Decidable l.CitationsChecked :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

theorem anchorsConfirmed_of_citationsChecked {l : Ledger} (h : l.CitationsChecked) :
    l.AnchorsConfirmed := fun c hc => (h c hc).2

/--
Documents not checked since a cutoff date, including those never checked.

`docs/VALIDATION.md` §1 requires reference drift to be reviewed rather than to
happen silently. This is the query a drift review runs: everything not
re-checked since the last review date. An `unverified` document has no check
date and is always included, which is the conservative reading.
-/
def staleSince (l : Ledger) (cutoff : Date) : List SourceDocument :=
  l.documents.filter fun d =>
    match d.retrieval.checkedOn with
    | none => true
    | some on => !decide (Date.le cutoff on)

/--
Documents whose loss would be a release blocker.

`docs/VALIDATION.md` §1 allows a broken link to fall back to a reviewed cached
copy; a `referenceOnly` document has no such copy, so its link rot blocks
release. Both vendor manuals are in this category, and the ledger says so
plainly rather than leaving the reader to assume a cache exists.
-/
def noFallback (l : Ledger) : List SourceDocument :=
  l.documents.filter (fun d => !d.policy.hasFallback)

/--
Documents confirmed not to be served at their recorded location, and with no
lawful cached copy.

This is the list that blocks a release under `docs/VALIDATION.md` §1. It is a
separate query from `noFallback` because most sources have no fallback and are
perfectly reachable; only the intersection is a blocker.
-/
def releaseBlockers (l : Ledger) : List SourceDocument :=
  l.documents.filter (fun d => decide d.IsReleaseBlocker)

/-- Documents this corpus has never fetched for itself. -/
def unverifiedSources (l : Ledger) : List SourceDocument :=
  l.documents.filter (fun d => d.retrieval == .unverified)

/--
Every source behind this ledger has been fetched and confirmed.

A profile that wants `docs/DECISIONS.md` 21's citations to mean something a
reader can act on demands this, rather than accepting a URL nobody has tried.
-/
def SourcesVerified (l : Ledger) : Prop :=
  ∀ d ∈ l.documents, d.retrieval.isVerified = true

instance (l : Ledger) : Decidable l.SourcesVerified :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- A ledger whose sources are all verified has no release blockers. -/
theorem releaseBlockers_eq_nil_of_verified {l : Ledger} (h : l.SourcesVerified) :
    l.releaseBlockers = [] :=
  List.filter_eq_nil_iff.mpr fun d hd => by
    simpa using SourceDocument.not_blocker_of_verified (h d hd)

/-- End-to-end checked citations rest on verified sources. -/
theorem sourcesVerified_of_citationsChecked {l : Ledger} (h : l.CitationsChecked) :
    l.SourcesVerified := by
  intro d hd
  match List.mem_map.mp hd with
  | ⟨c, hc, hcd⟩ => exact hcd ▸ (h c hc).1

/--
Common rules that record a resolved vendor disagreement.

`docs/VALIDATION.md` §6 requires "known discrepancies, errata, and mitigations"
and §2 requires that "Disagreement is preserved as a finding; majority vote does
not establish truth." A `weakerCommon` rule is a preserved finding whose
mitigation is the weakening, and it stays visible here after resolution.
-/
def divergences (l : Ledger) : List CommonRule :=
  l.common.filter CommonRule.isDivergent

/-- Refinements supplied by one vendor. -/
def refinementsOf (l : Ledger) (v : Vendor) : List VendorRefinement :=
  l.refinements.filter (fun r => r.vendor = v)

theorem mem_refinementsOf {l : Ledger} {v : Vendor} {r : VendorRefinement}
    (h : r ∈ l.refinementsOf v) : r ∈ l.refinements ∧ r.vendor = v := by
  have := List.mem_filter.mp h
  exact ⟨this.1, by simpa using this.2⟩

end Ledger

end Grass.ISA.X86
