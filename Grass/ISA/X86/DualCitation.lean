import Grass.ISA.X86.Citation

/-!
# Dual citation and the common x86-64 intersection

`docs/DECISIONS.md` 15: "The initial ISA is a dual-cited common x86-64
intersection with Intel and AMD refinements and separate validation."

`docs/INSTRUCTIONS.md` §7 spells out the mechanism: "Every common rule records
both vendor citations with document revision and anchor. Conflicts select the
weaker common guarantee, split into refinements, or exclude the construct."

This module makes that a construction rather than a review checklist. A
`CommonRule` cannot be built without an Intel anchor *and* an AMD anchor, and
neither can a `Excluded`, because excluding a construct is a claim about what
both vendors say and needs both sides on the record.

## Three failure modes, two of them closed here

A dual-citation field that is merely a pair of citations closes none of them.

1. **Both citations from one vendor.** A rule with two Intel anchors reads as
   dual-cited in a report. `intelPublisher` and `amdPublisher` check each side
   against `Vendor.publisher`, so a lopsided pair does not typecheck.

2. **A citation that names no location.** `docs/REFERENCES.md` rejects the
   collection landing page as an anchor. `intelWellFormed`/`amdWellFormed`
   require `Citation.WellFormed`, which rejects a blank section, an empty
   subject list, and a blank locator.

3. **Citations that are not about the subject.** An Intel anchor for `MOV`
   paired with an AMD anchor for `ADD` satisfies "two vendors, two anchors" and
   establishes nothing about either. `intelCovers` and `amdCovers` require both
   sides to *list* the subject, and the subject is a type index so a value built
   for one rule cannot be moved to another.

   **This third one is not closed, and the check is weaker than it looks.**
   `Citation.subjects` is a list of names the record's author types in. Nothing
   relates it to the cited passage, nothing checks the names resolve to
   declarations, and one anchor may list every subject in the profile — so a
   preface citing "the whole manual" for all nine rules satisfies every
   obligation here. Whether an anchor is *about* what it claims is a fact about
   the manual's text, which no type in Lean can decide. It is an **open
   obligation** discharged by a reviewer following `Citation.locator` and
   recording the result in `Citation.confirmed`, and until that field is set the
   ledger reports the anchor as unconfirmed.

The obligations that *are* mechanised are `by decide` on honest concrete data:
free when the record is real, unprovable when it is not.

## What this module does not claim

Recording that both vendors state a guarantee is not a proof that the guarantee
holds, and this corpus never treats it as one. `docs/VALIDATION.md` §1: "Tools
and hardware are fallible oracles." A dual citation says the modeled rule is the
*intersection of two written contracts*, which is what `docs/DECISIONS.md` 15
selects as the initial ISA's authority. Physical agreement is a separate
campaign, run "independently on Intel and AMD hardware" per
`docs/VALIDATION.md` §3.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Cite

/--
An x86-64 architectural authority.

Deliberately closed, unlike `Grass.Core.Name`. `docs/FOUNDATION.md` law 8 forbids
closed sum types where new members are expected, and this is the case where none
are: `docs/DECISIONS.md` 15 defines the common profile as the intersection of
*these two* contracts. A third vendor's manual would not join this type; it
would be a new profile with its own intersection, because "intersection" is only
meaningful relative to a fixed set of contracts.
-/
inductive Vendor where
  /-- Intel Corporation, publisher of the Intel 64 and IA-32 SDM. -/
  | intel
  /-- Advanced Micro Devices, publisher of the AMD64 APM. -/
  | amd
deriving DecidableEq, Repr, Inhabited

namespace Vendor

/-- The publisher name a citation from this vendor must carry.

These strings are the join key between a `SourceDocument` and a vendor, so they
are defined once here rather than repeated at each document. -/
def publisher : Vendor → Name
  | .intel => ⟨"Intel Corporation"⟩
  | .amd => ⟨"Advanced Micro Devices, Inc."⟩

/-- The other vendor. -/
def other : Vendor → Vendor
  | .intel => .amd
  | .amd => .intel

@[simp] theorem other_other (v : Vendor) : v.other.other = v := by cases v <;> rfl

theorem other_ne (v : Vendor) : v.other ≠ v := by cases v <;> decide

theorem publisher_injective {a b : Vendor} (h : a.publisher = b.publisher) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

/-- A short stable tag for reports and test-environment records. -/
def tag : Vendor → String
  | .intel => "intel"
  | .amd => "amd"

end Vendor

/--
Both vendors' anchors for one named subject.

The subject is a type index of `DualCitation`, not a field, so a value built for
one rule cannot be reused for another. Moving a dual citation to a different
rule is a type error, which is the point: a citation's authority does not
transfer.
-/
structure DualCitation (subject : Name) where
  /-- Intel's anchor for `subject`. -/
  intel : Citation
  /-- AMD's anchor for `subject`. -/
  amd : Citation
  /-- Intel's citation really is published by Intel. -/
  intelPublisher : intel.publisher = Vendor.intel.publisher
  /-- AMD's citation really is published by AMD. -/
  amdPublisher : amd.publisher = Vendor.amd.publisher
  /-- Intel's citation is authority for this exact subject. -/
  intelCovers : intel.covers subject = true
  /-- AMD's citation is authority for this exact subject. -/
  amdCovers : amd.covers subject = true
  /-- Intel's citation has a usable anchor, a subject, and a locator. -/
  intelWellFormed : intel.WellFormed
  /-- AMD's citation has a usable anchor, a subject, and a locator. -/
  amdWellFormed : amd.WellFormed

namespace DualCitation

variable {subject : Name}

/-- The citation from a chosen vendor. -/
def forVendor (d : DualCitation subject) : Vendor → Citation
  | .intel => d.intel
  | .amd => d.amd

/-- Each side's citation is published by the vendor it is filed under.

The two `mk` fields say this for a literal `.intel`/`.amd`; this says it for a
vendor held in a variable, which is what a report generator has. -/
theorem forVendor_publisher (d : DualCitation subject) (v : Vendor) :
    (d.forVendor v).publisher = v.publisher := by
  cases v
  · exact d.intelPublisher
  · exact d.amdPublisher

/-- Each side's citation is authority for this subject. -/
theorem forVendor_covers (d : DualCitation subject) (v : Vendor) :
    (d.forVendor v).covers subject = true := by
  cases v
  · exact d.intelCovers
  · exact d.amdCovers

/-- Each side's citation is well-formed. -/
theorem forVendor_wellFormed (d : DualCitation subject) (v : Vendor) :
    (d.forVendor v).WellFormed := by
  cases v
  · exact d.intelWellFormed
  · exact d.amdWellFormed

/-- The two sides are never the same document *and* anchor for both vendors,
because their publishers differ. A single source cannot dual-cite itself, since
`Vendor.publisher_injective` forces the two apart. -/
theorem intel_ne_amd (d : DualCitation subject) : d.intel ≠ d.amd := by
  intro h
  have : Vendor.intel.publisher = Vendor.amd.publisher := by
    rw [← d.intelPublisher, ← d.amdPublisher, h]
  exact absurd (Vendor.publisher_injective this) (by decide)

/-- Both citations, Intel first. -/
def citations (d : DualCitation subject) : List Citation := [d.intel, d.amd]

/-- Both cited documents, for a drift or trust-ledger report. -/
def documents (d : DualCitation subject) : List SourceDocument :=
  [d.intel.document, d.amd.document]

@[simp] theorem documents_eq_map (d : DualCitation subject) :
    d.documents = d.citations.map (·.document) := rfl

/-- Whether link rot on either side has a lawful fallback.

`docs/VALIDATION.md` §1 makes a broken link with no reviewed cached copy a
release blocker. Both vendor manuals are `referenceOnly` in this corpus, so this
is normally `false` and the ledger says so rather than implying a cache exists. -/
def bothHaveFallback (d : DualCitation subject) : Bool :=
  d.intel.hasFallback && d.amd.hasFallback

/--
Build a dual citation, deciding every obligation, or report which one failed.

This is the route for tooling that reads citation data it did not write.
Corpus-internal rules construct the structure directly and discharge the fields
with `by decide`, which gives a better error at the failing field.
-/
def check (subject : Name) (intel amd : Citation) :
    Except String (DualCitation subject) :=
  if hip : intel.publisher = Vendor.intel.publisher then
    if hap : amd.publisher = Vendor.amd.publisher then
      if hic : intel.covers subject = true then
        if hac : amd.covers subject = true then
          if hiw : intel.WellFormed then
            if haw : amd.WellFormed then
              .ok { intel := intel, amd := amd
                    intelPublisher := hip, amdPublisher := hap
                    intelCovers := hic, amdCovers := hac
                    intelWellFormed := hiw, amdWellFormed := haw }
            else .error s!"AMD citation for {subject} is not well-formed"
          else .error s!"Intel citation for {subject} is not well-formed"
        else .error s!"AMD citation does not list subject {subject}"
      else .error s!"Intel citation does not list subject {subject}"
    else .error s!"citation filed as AMD is published by {amd.publisher}"
  else .error s!"citation filed as Intel is published by {intel.publisher}"

theorem check_ok_intel {subject : Name} {intel amd : Citation}
    {d : DualCitation subject} (h : check subject intel amd = .ok d) :
    d.intel = intel := by
  unfold check at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · split at h
            · exact congrArg DualCitation.intel (Except.ok.inj h).symm
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end DualCitation

/--
Why the modeled common rule is what it is.

`docs/INSTRUCTIONS.md` §7 gives three dispositions for a vendor conflict:
"select the weaker common guarantee, split into refinements, or exclude the
construct." Splitting and excluding produce a `VendorRefinement` and an
`Excluded`; only the first two cases produce a common rule, and they are these.
-/
inductive CommonBasis where
  /--
  Grass reads both manuals as stating the guarantee, but nobody has followed
  either anchor to check.

  Deliberately **first**, so it is what `Inhabited` produces and what a rule
  falls back to. It is also the only honest basis for a rule whose anchors are
  unconfirmed, which today is all of them.
  -/
  | assertedPendingConfirmation
  /--
  Both manuals state the same guarantee, and someone has confirmed both anchors
  on the given dates.

  What the type enforces, precisely. `CommonRule.agreedIsConfirmed` requires the
  dates to match both citations' `Citation.confirmed`, requires both citations
  to be `Citation.FullyChecked`, and requires both dates to be
  `Date.WellFormed`. `FullyChecked` adds `SourceDocument.retrieval.isVerified`.

  That is weaker than an earlier version of this paragraph claimed. It said the
  status is one "this corpus sets by probing the location, not by an author
  typing a date"; no probe exists in this repository, and `SourceDocument` is a
  public structure, so an invented document with `retrieval := .verified` is as
  easy to write. A reviewer built one. The conjunct bites against the documents
  this corpus registers -- the AMD one is recorded dead -- and not against an
  invented one; `Grass.ISA.X86.Rules.all_registered` is what pins the common
  profile's rules to the registered documents.

  What it does **not** enforce is that anyone read the manual. An earlier
  version of this docstring said the constructor "cannot be written for a
  document nobody has opened", and a reviewer disproved it in about a dozen
  lines: with only the date-matching conjunct, the obligation was a consistency
  check between two fields the same author writes, so typing the same fabricated
  date twice discharged it -- over a document recorded as dead, with a date of
  0000-00-00. Requiring `FullyChecked` and `Date.WellFormed` kills that
  particular construction. It does not make agreement *evidence*: no proposition
  in Lean can witness a human opening a PDF, and `Citation.confirmed` remains a
  claim.

  The honest statement is narrower and still worth having: via
  `Citation.FullyChecked`, this constructor cannot be written for a document the
  corpus records as unretrievable. That is why no rule in this profile claims it
  today -- the AMD manual is dead. The anchor-following obligation stays open,
  and the ledger reports it.
  -/
  | agreed (intelConfirmed amdConfirmed : Date)
  /-- The manuals differ and the modeled rule is deliberately weaker than at
  least one of them. Both notes record what each vendor actually states, so a
  reviewer can check that the modeled rule really is implied by both rather than
  by neither. -/
  | weakerCommon (intelStates amdStates : String)
deriving DecidableEq, Repr, Inhabited

namespace CommonBasis

/-- Whether this basis records a vendor disagreement.

A disagreement is a finding under `docs/VALIDATION.md` §7 and is reported even
though it was resolved, because the resolution is a restriction that a later
reader must be able to see. -/
def isDivergent : CommonBasis → Bool
  | .assertedPendingConfirmation => false
  | .agreed _ _ => false
  | .weakerCommon _ _ => true

/-- Whether the basis has actually been checked against both manuals. -/
def isConfirmed : CommonBasis → Bool
  | .agreed _ _ => true
  | _ => false

end CommonBasis

/--
One rule of the common x86-64 profile.

`statement` is Grass's own paraphrase of the modeled guarantee, written to be
checked against both anchors. It is not a transcript of either manual; see
`Grass/ISA/X86/Citation.lean` on why no citation carries the source text.
-/
structure CommonRule where
  /-- The declaration this rule is about. -/
  subject : Name
  /-- Grass's statement of the modeled guarantee, in reviewable prose. -/
  statement : String
  /-- Both vendors' anchors for exactly this subject. -/
  citation : DualCitation subject
  /-- Whether the vendors agreed, or the rule is the weaker intersection. -/
  basis : CommonBasis
  /--
  `CommonBasis.agreed` may only be claimed when both citations are checkable end
  to end and confirmed on the dates it names.

  This is what stops an `agreed` basis being free. It is *not* what makes an
  unfounded agreement claim impossible, and the difference matters: a reviewer
  built a `CommonRule` claiming `agreed` over two dead documents when this
  obligation was only that the dates match `Citation.confirmed`, because both
  the basis and the confirmation dates are fields the same author writes, so the
  obligation was self-consistency rather than evidence.

  The `FullyChecked` conjuncts add `SourceDocument.retrieval.isVerified`, and
  `Date.WellFormed` rules out the placeholder date the same reviewer used.
  Neither is unforgeable: a later reviewer invented a document carrying
  `.verified` and rebuilt the attack, so the conjuncts bind only against the
  registered documents. `Grass.ISA.X86.Rules.all_registered` supplies that
  pinning for the profile. What remains unenforceable either way is whether
  anyone followed the anchor; see `CommonBasis.agreed`.

  The default proof discharges the obligation for every other basis, where the
  hypothesis is contradictory, so only an actual `agreed` rule pays anything.
  -/
  agreedIsConfirmed : ∀ di da, basis = .agreed di da →
      citation.intel.confirmed = some di ∧ citation.amd.confirmed = some da ∧
        citation.intel.FullyChecked ∧ citation.amd.FullyChecked ∧
          di.WellFormed ∧ da.WellFormed := by
    intro _ _ h; exact absurd h (by simp)

namespace CommonRule

/-- The documents this rule depends on. -/
def documents (r : CommonRule) : List SourceDocument := r.citation.documents

/-- Whether this rule records a resolved vendor disagreement. -/
def isDivergent (r : CommonRule) : Bool := r.basis.isDivergent

/-- Whether this rule's basis has been checked against both manuals.

`Ledger` reports the rules where it has not, which is every rule today. -/
def basisConfirmed (r : CommonRule) : Bool := r.basis.isConfirmed

end CommonRule

/--
A guarantee available from one vendor only.

`docs/INSTRUCTIONS.md` §7: "Instructions outside the intersection require a
vendor/feature refinement." A refinement is single-cited by construction — that
is what makes it a refinement — so it carries a plain `Citation` plus proof that
the citation is from the vendor it claims.

`supersedes` names the common rule this refinement strengthens, when there is
one. A refinement of nothing is a guarantee the common profile does not have at
all, which is a different and weaker thing than strengthening a common rule, and
the ledger reports them differently.
-/
structure VendorRefinement where
  /-- The declaration this refinement is about. -/
  subject : Name
  /-- The vendor whose contract supplies it. -/
  vendor : Vendor
  /-- Grass's statement of the refined guarantee. -/
  statement : String
  /-- That vendor's anchor. -/
  citation : Citation
  /-- The citation really is published by the named vendor. -/
  publisherMatches : citation.publisher = vendor.publisher
  /-- The citation is authority for this exact subject. -/
  covers : citation.covers subject = true
  /-- The citation has a usable anchor, a subject, and a locator. -/
  wellFormed : citation.WellFormed
  /-- The common rule this strengthens, if any. -/
  supersedes : Option Name

/--
A construct the common profile does not model at all.

Exclusion is the third disposition in `docs/INSTRUCTIONS.md` §7. It carries a
`DualCitation` rather than a single citation because excluding a construct is a
claim about *both* contracts: that no common guarantee can be stated. Recording
only the vendor whose text prompted the exclusion would leave the other side
unchecked, and a later reader could not tell whether the second manual had even
been consulted.
-/
structure Excluded where
  /-- The construct not modeled. -/
  subject : Name
  /-- Why no common guarantee is available. -/
  reason : String
  /-- Both vendors' anchors for the construct being excluded. -/
  citation : DualCitation subject

end Grass.ISA.X86
