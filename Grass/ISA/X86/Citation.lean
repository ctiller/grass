import Grass.Core.Name

/-!
# Citation records

`docs/VALIDATION.md` §1 fixes the shape of a citation record: "stable identity,
title, publisher, revision/date, retrieval location, exact anchor, license/cache
policy, affected declarations, and review instructions for locating and checking
the source text." This module is that record.

## Why this is a type and not a comment

`docs/DECISIONS.md` 21 requires *every* modeled instruction and API behavior to
carry vendor citations. A convention enforced by review alone degrades: a
docstring URL cannot be counted, cannot be checked for a missing anchor, and
cannot be inverted into the per-profile trust ledger `docs/VALIDATION.md` §6
requires a profile to publish. Making the record a value means the ledger is
derived from the model rather than maintained beside it, and means a rule with
no anchor fails to elaborate rather than passing review unnoticed.

## Why there is no quotation field

A reviewer must be able to find and check the source text, so the record carries
a `locator` — instructions for reaching the passage. It deliberately does not
carry the passage. The Intel SDM and the AMD APM are copyrighted, and a corpus
that accumulated their text would be redistributing them under the guise of
citation. `docs/VALIDATION.md` §1 asks for "review instructions for locating and
checking the source text", which is what a locator is.

The `statement` a Grass rule carries is therefore Grass's own paraphrase of the
modeled guarantee, written to be checked against the anchor, never a transcript
of it.

## Why collection links are not anchors

`docs/REFERENCES.md` says of the Intel and AMD manual landing pages: "These
collection links are discovery roots, not sufficient declaration-level anchors."
`SourceDocument.url` is the discovery root; `Anchor` is the declaration-level
part, and it is a separate mandatory field precisely so that a URL cannot stand
in for one.

**Custody note.** This module is generic and belongs in `Grass.Core` beside
`Grass.Core.Name`, which carries the same kind of note under
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §2. It is homed under the x86 tree because
that is the lowest module in this agent's ownership (`Grass/ISA/X86/**`,
`Grass/ABI/Win64/**`, `Grass/Platform/Win32/**`). The namespace is already
`Grass.Cite`, so lifting it is a file move and not a rename across consumers.
-/

namespace Grass.Cite

open Grass.Core

/-- A calendar date, used for document revisions and retrieval dates.

Structured rather than a formatted string because `docs/VALIDATION.md` §1
requires reference drift to be *reviewed*: "new revisions do not silently
replace the revision against which a theorem was written." Comparing revisions
is a thing a tool should be able to do. -/
structure Date where
  /-- The year. -/
  year : Nat
  /-- The month, 1-12. -/
  month : Nat
  /-- The day, 1-31. -/
  day : Nat
deriving DecidableEq, Repr, Inhabited

namespace Date

/-- A date is well-formed when its month and day are in range.

This is a shape check, not a calendar: it does not know that February has 28
days. It exists to catch a transposed field, which is the realistic error. -/
def WellFormed (d : Date) : Prop :=
  1 ≤ d.month ∧ d.month ≤ 12 ∧ 1 ≤ d.day ∧ d.day ≤ 31

instance (d : Date) : Decidable d.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Chronological order, as a lexicographic comparison of year, month, day. -/
def le (a b : Date) : Prop :=
  a.year < b.year ∨
    (a.year = b.year ∧
      (a.month < b.month ∨ (a.month = b.month ∧ a.day ≤ b.day)))

instance (a b : Date) : Decidable (Date.le a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem le_refl (d : Date) : Date.le d d :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, Nat.le_refl _⟩⟩

end Date

/--
How a source may be retained.

`docs/VALIDATION.md` §1 requires a license/cache policy, and also requires that
a broken link "uses a reviewed cached copy or is a release blocker according to
the reference policy". The two are the same question: whether this corpus is
permitted to hold a copy determines what happens when the link rots.
-/
inductive CachePolicy where
  /-- Redistribution is not permitted; the corpus holds the anchor only. A dead
  link is a release blocker, because there is no lawful fallback. -/
  | referenceOnly
  /-- A copy may be retained in the reviewed reference cache under the named
  terms. A dead link falls back to that copy. -/
  | cacheable (terms : String)
  /-- The source is openly licensed under the named license and may be
  redistributed with the corpus. -/
  | redistributable (license : String)
deriving DecidableEq, Repr, Inhabited

namespace CachePolicy

/-- Whether a dead retrieval link has a lawful fallback under this policy.

`referenceOnly` sources have none, which is why link rot on a vendor manual is a
release blocker rather than an inconvenience. -/
def hasFallback : CachePolicy → Bool
  | .referenceOnly => false
  | .cacheable _ => true
  | .redistributable _ => true

end CachePolicy

/--
What this corpus knows about whether a document's retrieval location still
serves the document.

## Why this is not a bare retrieval date

`docs/VALIDATION.md` §1 requires that a broken link "uses a reviewed cached copy
or is a release blocker according to the reference policy", which presumes
someone can tell that a link is broken. For the two authorities
`docs/DECISIONS.md` 15 depends on, an HTTP status check answers wrongly in both
directions, as measured on 2026-09-02:

- `intel.com` returns 403 to an automated request while serving the manual
  normally to a browser, so a status checker reports a live source dead.
- `docs.amd.com` is a client-routed single-page application that returns 200
  with an identical 2575-byte shell for every path, including paths that render
  a 404. A status checker reports a dead source live.

A CI link check built on status codes would therefore have reported the corpus
healthy while its AMD anchor was unreachable. `livenessProbe` on
`SourceDocument` exists so a check can assert on *content* instead, and this
type records the outcome so the ledger can report it rather than leaving a
reader to assume an unchecked URL works.
-/
inductive RetrievalStatus where
  /-- Fetched on this date, and the document's liveness probe matched. -/
  | verified (on : Date)
  /-- Recorded from a secondary source and never fetched by this corpus. Not a
  failure, but not evidence either: a profile may require better. -/
  | unverified
  /-- Fetched on this date and the location did not serve the document. Under a
  `referenceOnly` policy this is a release blocker, because there is no lawful
  cached copy to fall back to. -/
  | dead (on : Date) (note : String)
deriving DecidableEq, Repr, Inhabited

namespace RetrievalStatus

/-- Whether this corpus has confirmed the location serves the document. -/
def isVerified : RetrievalStatus → Bool
  | .verified _ => true
  | _ => false

/-- Whether this corpus has confirmed the location does *not* serve it. -/
def isDead : RetrievalStatus → Bool
  | .dead _ _ => true
  | _ => false

/-- The date of the last check, where one was made. -/
def checkedOn : RetrievalStatus → Option Date
  | .verified d => some d
  | .dead d _ => some d
  | .unverified => none

theorem not_dead_of_verified {s : RetrievalStatus} (h : s.isVerified = true) :
    s.isDead = false := by cases s <;> simp_all [isVerified, isDead]

end RetrievalStatus

/--
An external document, identified stably and independently of any one citation
into it.

Documents are shared: a hundred instruction rules cite one revision of the Intel
SDM. Separating the document from the anchor is what makes a revision bump a
single reviewed edit rather than a hundred, and is what lets a drift report say
"these rules were written against revision X" without scanning prose.
-/
structure SourceDocument where
  /-- Stable identity for this document *and revision*, used as the join key in
  ledgers and drift reports. Two revisions of one manual are two documents. -/
  id : Name
  /-- The document's title as published. -/
  title : String
  /-- The publishing organization. Compared by value: `docs/DECISIONS.md` 15
  needs to check that an Intel citation really is Intel's. -/
  publisher : Name
  /-- The publisher's own revision, version, or publication number. -/
  revision : String
  /-- The revision's publication date, where the publisher states one. -/
  published : Option Date
  /-- Where the document was retrieved. `docs/REFERENCES.md` warns that a
  collection landing page is a discovery root, not an anchor; this field is
  allowed to be such a root because `Anchor` carries the precise part. -/
  url : String
  /-- Text that must appear in whatever `url` serves for the retrieval to count
  as having reached this document. See `RetrievalStatus` for why a status code
  is not sufficient for either of the two x86 authorities. `none` means no
  probe has been chosen, which a profile may reject. -/
  livenessProbe : Option String
  /-- What this corpus knows about whether `url` still serves the document. -/
  retrieval : RetrievalStatus
  /-- Whether this corpus may retain a copy, and on what terms. -/
  policy : CachePolicy
deriving DecidableEq, Repr, Inhabited

namespace SourceDocument

/--
This document is a release blocker: its location does not serve it and its
license gives no lawful fallback.

`docs/VALIDATION.md` §1 offers exactly two outcomes for a broken link, and this
is the predicate that separates them.
-/
def IsReleaseBlocker (d : SourceDocument) : Prop :=
  d.retrieval.isDead = true ∧ d.policy.hasFallback = false

instance (d : SourceDocument) : Decidable d.IsReleaseBlocker :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A verified document is never a release blocker. -/
theorem not_blocker_of_verified {d : SourceDocument}
    (h : d.retrieval.isVerified = true) : ¬ d.IsReleaseBlocker := by
  intro hb
  have := RetrievalStatus.not_dead_of_verified h
  simp [IsReleaseBlocker, this] at hb

end SourceDocument

/--
The declaration-level position inside a document.

Every field beyond `section_` is optional because vendors structure documents
differently, but `section_` is mandatory: an anchor that names no location is
the whole-document citation `docs/REFERENCES.md` rejects — "a whole-RFC citation
is not sufficient implementation metadata".
-/
structure Anchor where
  /-- The volume, where the document has volumes. The Intel SDM and the AMD APM
  both do. -/
  volume : Option String
  /-- The chapter or section number, as printed. Mandatory. -/
  section_ : String
  /-- The section's printed heading, so a reviewer can confirm the number
  resolved to the passage intended when numbering shifts between revisions. -/
  heading : Option String
  /-- A table or figure identifier, where the fact lives in one. Encoding facts
  usually do. -/
  table : Option String
  /-- The printed page, where the document paginates stably. -/
  page : Option Nat
deriving DecidableEq, Repr, Inhabited

namespace Anchor

/-- An anchor is usable when it names a section.

`docs/VALIDATION.md` §1 requires an *exact* anchor. The empty string is the
degenerate value a partially filled record would carry, so it is rejected here
rather than discovered during review. -/
def Usable (a : Anchor) : Prop := a.section_ ≠ ""

instance (a : Anchor) : Decidable a.Usable := inferInstanceAs (Decidable (¬ _))

/-- An anchor naming only a section of a volume. -/
def ofSection (volume section_ : String) : Anchor :=
  { volume := some volume, section_ := section_, heading := none,
    table := none, page := none }

/-- An anchor naming a table within a section of a volume. -/
def ofTable (volume section_ table : String) : Anchor :=
  { volume := some volume, section_ := section_, heading := none,
    table := some table, page := none }

@[simp] theorem usable_ofSection {volume section_ : String} (h : section_ ≠ "") :
    (Anchor.ofSection volume section_).Usable := h

@[simp] theorem usable_ofTable {volume section_ table : String} (h : section_ ≠ "") :
    (Anchor.ofTable volume section_ table).Usable := h

end Anchor

/--
One citation: a document, a position in it, and instructions for checking it.

`subjects` is the "affected declarations" field of `docs/VALIDATION.md` §1. The
primary link between a declaration and its authority is attachment — a modeled
rule holds its citations — but the trust ledger has to be publishable *from the
citation side*, and inverting attachment requires walking every model. Naming
the subjects here keeps the ledger derivable from the citations alone.
-/
structure Citation where
  /-- The document and revision cited. -/
  document : SourceDocument
  /-- Where in it. -/
  anchor : Anchor
  /-- The declarations this citation is authority for. -/
  subjects : List Name
  /-- How a reviewer finds and checks the passage: what to search for, which
  column of a table, what the neighbouring rows are. Not a transcript of the
  passage; see this module's header. -/
  locator : String
  /-- When someone last opened the document and confirmed this anchor resolves
  to the passage the `subjects` are modeled from, if anyone has.

  A live document is not a confirmed anchor. `SourceDocument.retrieval` says the
  URL serves the manual; this says a human or tool followed `anchor` inside it
  and found the right text. Section and table numbers drift between revisions
  even when the prose does not, so the two facts fail independently and are
  recorded independently.

  `none` is an honest and common state — an anchor written from working
  knowledge and awaiting confirmation. It is deliberately not a
  `WellFormed` failure, because refusing to record a citation until it is
  confirmed produces no citation at all, which is worse. The ledger reports the
  unconfirmed ones instead. -/
  confirmed : Option Date
deriving DecidableEq, Repr, Inhabited

namespace Citation

/--
A citation is well-formed when its anchor is usable, it names at least one
subject, and it tells a reviewer how to check it.

`docs/VALIDATION.md` §1 requires all three, and each has a degenerate value that
would otherwise pass unnoticed: a blank section, an empty subject list, and a
blank locator are what a record filled in halfway looks like.
-/
def WellFormed (c : Citation) : Prop :=
  c.anchor.Usable ∧ c.subjects ≠ [] ∧ c.locator ≠ ""

instance (c : Citation) : Decidable c.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Whether this citation is authority for the named declaration. -/
def covers (c : Citation) (subject : Name) : Bool := c.subjects.contains subject

/-- The publisher of the cited document. -/
def publisher (c : Citation) : Name := c.document.publisher

/-- Whether a dead link to this citation's document has a lawful fallback. -/
def hasFallback (c : Citation) : Bool := c.document.policy.hasFallback

/-- Whether someone has followed this anchor inside the document and found the
passage. See `Citation.confirmed`. -/
def isConfirmed (c : Citation) : Bool := c.confirmed.isSome

/--
This citation is checkable end to end: the document is served at its recorded
location, and the anchor has been followed inside it.

The two conjuncts are the two independent ways a citation stops being usable.
`docs/VALIDATION.md` §1 wants both — a stable retrieval location *and* an exact
anchor — and `FullyChecked` is what a record satisfying only one of them fails,
because a reviewer cannot act on it. -/
def FullyChecked (c : Citation) : Prop :=
  c.document.retrieval.isVerified = true ∧ c.isConfirmed = true

instance (c : Citation) : Decidable c.FullyChecked :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem covers_of_mem {c : Citation} {subject : Name}
    (h : subject ∈ c.subjects) : c.covers subject = true := by
  simpa [covers] using h

theorem mem_of_covers {c : Citation} {subject : Name}
    (h : c.covers subject = true) : subject ∈ c.subjects := by
  simpa [covers] using h

end Citation

end Grass.Cite
