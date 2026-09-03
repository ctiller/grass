import Grass.ISA.X86.DualCitation

/-!
# The two x86-64 architectural authorities

`docs/REFERENCES.md` names the sources `docs/DECISIONS.md` 15 makes the common
profile out of. This module turns those two entries into the values every rule
in `Grass/ISA/X86/**` cites, so a revision bump or a moved URL is one reviewed
edit here rather than an edit at every rule.

## State of the two sources on 2026-09-02

Both were checked from this working copy on 2026-09-02, in a full browser rather
than by HTTP status, for the reasons in `Grass.Cite.RetrievalStatus`.

- **Intel** is live. The collection page serves the combined volume set at
  version **092**, page-dated 2026-08-19. `docs/REFERENCES.md` pinned no Intel
  revision at all, which `docs/VALIDATION.md` §1 requires ("stable identity,
  title, publisher, revision/date"); this module pins 092.

- **AMD is dead.** The URL `docs/REFERENCES.md` pins,
  `https://docs.amd.com/v/u/en-US/40332_4.09_APM_PUB`, renders a 404 and
  redirects to the portal root. So does the `4.10` slug that search engines
  still index, and so does every `www.amd.com/content/dam/.../40332*.pdf` path
  tried. AMD appears to have retired the `/v/u/en-US/` scheme for the
  Technical Information Portal.

  The AMD APM is `referenceOnly`, so `docs/VALIDATION.md` §1 leaves exactly one
  disposition: release blocker. `Ledger.releaseBlockers` reports it, and it is
  recorded here as `.dead` rather than quietly left as a plausible-looking URL.

## What the dead AMD link does and does not block

It does not block *writing* the common profile. A `DualCitation` names a
document, a volume, a section and a heading; those are properties of the manual,
not of AMD's web hosting. The AMD anchors below are written against the APM's
stable structure and carry `confirmed := none`.

It does block *accepting* the profile: `Ledger.CitationsChecked` is false while
any anchor is unconfirmed or any document is dead, and re-pinning the AMD URL is
a single edit to `amd64Apm409` that lifts every rule at once. That is the whole
reason `SourceDocument` is a shared value and not a string repeated at each
citation.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Cite

/-- The date the sources below were checked. -/
def sourceCheckDate : Date := ⟨2026, 9, 2⟩

/-- The date the Intel anchors were followed inside the manual.

Distinct from `sourceCheckDate`, because the two facts are independent: the
first says the URL served the document, the second says a section number
resolved to the passage a rule is modeled from. `Grass.Cite.Citation.confirmed`
carries this one. -/
def intelAnchorCheckDate : Date := ⟨2026, 9, 3⟩

/--
Intel 64 and IA-32 Architectures Software Developer's Manual, combined volume
set, version 092.

`published` is the date the collection page carried for version 092
(2026-08-19). Intel dates the posting rather than printing a revision date on
the combined set, so that is the strongest date available and is recorded as
what it is.

The `url` is the collection page, which `docs/REFERENCES.md` correctly calls a
discovery root rather than an anchor. Every citation into this document supplies
its own `Anchor`; the combined PDF itself is reached from that page through
Intel's content ID 671200, which the locators name.

## How the confirmed anchors were confirmed

Anchors carrying `confirmed := some intelAnchorCheckDate` were followed inside
the per-volume PDFs from the same version-092 posting, not the combined set:
content ID 671199 for Vol. 2A and 671436 for Vol. 1, both fetched from
`cdrdv2.intel.com/v1/dl/getContent/`. Neither PDF is in the repository, by
instruction.

The reading was done by decompressing the PDFs' FlateDecode streams and
concatenating the parenthesised strings out of the text operators -- enough to
locate a heading and read the prose under it, which is what an anchor
confirmation needs. It is not a typesetting-faithful renderer, and two of its
limits bear on how much a quoted locator is worth. Parenthesised spans are
sometimes dropped where they nest, leaving a stray backslash; and stream order
is file order, not page order, so a section can arrive split -- Vol. 1
§3.4.1.1 did, which is why a first pass wrongly read it as not stating the
operand-size rule. Quotes in locators are therefore reconstructions of the
running prose, faithful in substance and close in wording, and a locator that
turns on exact punctuation should be re-checked in a real reader. Claims read
off table *layout* rather than prose (Tables 2-2, 2-3 and 2-5) are the ones to
treat most carefully; each is cross-checked against a prose statement or a
footnote in the locator that cites it.
-/
def intelSdm092 : SourceDocument :=
  { id := ⟨"intel-sdm-092"⟩
    title :=
      "Intel 64 and IA-32 Architectures Software Developer's Manual, " ++
      "Combined Volumes 1, 2A, 2B, 2C, 2D, 3A, 3B, 3C, 3D, and 4"
    publisher := Vendor.intel.publisher
    revision := "092"
    published := some ⟨2026, 8, 19⟩
    url := "https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html"
    livenessProbe := some "IA-32 Architectures Software Developer"
    retrieval := .verified sourceCheckDate
    policy := .referenceOnly }

/--
AMD64 Architecture Programmer's Manual, Volumes 1-5, publication 40332,
revision 4.09.

Identity and revision are as `docs/REFERENCES.md` pins them. The retrieval
location is recorded as dead; see this module's header for what was tried. The
revision is left at 4.09 rather than advanced to a number seen only in search
snippets, because `docs/VALIDATION.md` §1 wants the revision a theorem was
written against, and an unverified newer number would be neither.
-/
def amd64Apm409 : SourceDocument :=
  { id := ⟨"amd64-apm-40332-4.09"⟩
    title := "AMD64 Architecture Programmer's Manual, Volumes 1-5"
    publisher := Vendor.amd.publisher
    revision := "40332 rev. 4.09"
    published := none
    url := "https://docs.amd.com/v/u/en-US/40332_4.09_APM_PUB"
    livenessProbe := some "AMD64 Architecture Programmer"
    retrieval :=
      .dead sourceCheckDate
        ("renders a 404 and redirects to the docs.amd.com root; the /v/u/en-US/ " ++
         "scheme appears retired. HTTP status is 200 with an identical 2575-byte " ++
         "SPA shell for every path on this host, so a status-code link check " ++
         "does not detect this. Re-pin against the AMD Technical Information " ++
         "Portal.")
    policy := .referenceOnly }

/-- The document a vendor's citations are written against. -/
def Vendor.document : Vendor → SourceDocument
  | .intel => intelSdm092
  | .amd => amd64Apm409

@[simp] theorem Vendor.document_publisher (v : Vendor) :
    v.document.publisher = v.publisher := by cases v <;> rfl

/-!
## Volumes

The volumes of each manual that this profile cites, as `Anchor.volume` strings.
Named rather than spelled at each citation so that a typo cannot silently
produce an anchor into a volume that does not exist.
-/

namespace Volume

/-- Intel Vol. 2A: Instruction Set Reference, A-L, including the instruction
format chapter that owns REX, ModR/M, SIB and RIP-relative addressing. -/
def intelInstructionFormat : String := "Vol. 2A"

/-- Intel Vol. 1: Basic Architecture. -/
def intelBasic : String := "Vol. 1"

/-- Intel Vol. 3A: System Programming Guide, Part 1. -/
def intelSystem : String := "Vol. 3A"

/-- AMD Vol. 3: General-Purpose and System Instructions, whose Chapter 1 owns
instruction formats. -/
def amdInstructions : String := "Vol. 3"

/-- AMD Vol. 1: Application Programming. -/
def amdApplication : String := "Vol. 1"

/-- AMD Vol. 2: System Programming. -/
def amdSystem : String := "Vol. 2"

end Volume

/--
Build a citation into a vendor's manual.

Fixing the document from the vendor is what makes
`DualCitation.intelPublisher`/`amdPublisher` discharge by `rfl`, and removes the
only way to file a citation under the wrong vendor.

`table` is deliberately optional and usually omitted. Table *numbers* drift
between revisions while table *captions* do not, so the reliable instruction to
a reviewer is "find the table captioned X in this section", which belongs in
`locator`. A number goes in `Anchor.table` only once `Citation.confirmed`
records that it was checked against the revision this document pins.
-/
def cite (v : Vendor) (volume section_ heading : String) (subjects : List Name)
    (locator : String) (table : Option String := none)
    (confirmed : Option Date := none) : Citation :=
  { document := v.document
    anchor :=
      { volume := some volume, section_ := section_, heading := some heading,
        table := table, page := none }
    subjects := subjects
    locator := locator
    confirmed := confirmed }

@[simp] theorem cite_publisher (v : Vendor) (volume section_ heading : String)
    (subjects : List Name) (locator : String) (table : Option String)
    (confirmed : Option Date) :
    (cite v volume section_ heading subjects locator table confirmed).publisher =
      v.publisher := by
  simp [cite, Citation.publisher]

@[simp] theorem cite_subjects (v : Vendor) (volume section_ heading : String)
    (subjects : List Name) (locator : String) (table : Option String)
    (confirmed : Option Date) :
    (cite v volume section_ heading subjects locator table confirmed).subjects =
      subjects := rfl

end Grass.ISA.X86
