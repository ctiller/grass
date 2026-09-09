import Grass.ISA.X86.DualCitation

/-!
# Pinned x86-64 architectural authorities

Intel remains pinned to SDM revision 092. AMD's active citations migrate from
unretrievable combined APM revision 4.09 to the official revision 4.10 PDF,
retrieved on 2026-09-09. The old identity remains distinct and dead; it is not
renamed or treated as an equivalent edition.

The retrieved 4.10 cover and component headers identify Volume 1 as publication
24592 revision 3.25 (May 2026), and Volume 3 as publication 24594 revision 3.38
(July 2026). Existing claim subjects are mapped individually in Profile.lean.
The exact retrieval evidence, printed/PDF page mapping, limitations and negative
checks are recorded in docs/AMD_SOURCE_MIGRATION.md. No PDF is redistributed.

Retrieval verification is separate from anchor confirmation and common-basis
agreement. In particular, rexPrefixLayout's behavior for a misplaced REX remains
unconfirmed; moving its document does not settle that stronger claim.
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

/-- Date of the historical AMD portal and indexed download recheck.
See `amd64Apm409`; this is not an exhaustive archive search. -/
def amdRecheckDate : Date := ⟨2026, 9, 9⟩

/-- Date of the active AMD document retrieval and individual anchor inspection. -/
def amdAnchorCheckDate : Date := ⟨2026, 9, 9⟩

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

/-- Historical pin. Its exact portal route still fails; keep the old revision
identity and reference-only policy rather than relabeling it as a new edition. -/
def amd64Apm409 : SourceDocument :=
  { id := ⟨"amd64-apm-40332-4.09"⟩
    title := "AMD64 Architecture Programmer's Manual, Volumes 1-5"
    publisher := Vendor.amd.publisher
    revision := "40332 rev. 4.09"
    published := none
    url := "https://docs.amd.com/v/u/en-US/40332_4.09_APM_PUB"
    livenessProbe := some "AMD64 Architecture Programmer"
    retrieval := .dead amdRecheckDate
      ("The exact historical portal route and its indexed PDF content endpoint " ++
       "returned 404 on 2026-09-09. Search metadata advertising 4.09 is not a " ++
       "retrieval. Active citations are individually migrated to amd64Apm410; " ++
       "this record does not assert that every possible archive was searched.")
    policy := .referenceOnly }

/-- Official combined APM revision 4.10, with its own revision identity.

The PDF content endpoint is the download linked by AMD's publication page
https://docs.amd.com/v/u/en-US/40332_4.10_APM_Vol1-5_PUB. That page gives the
posting date used by published. The PDF cover says July 2026. The title probe
matches PDF metadata; it is only a liveness check, not revision/anchor proof.
Cover, component headers, prose, figures and table footnotes were inspected
separately. See docs/AMD_SOURCE_MIGRATION.md for exact reproducible locations. -/
def amd64Apm410 : SourceDocument :=
  { id := ⟨"amd64-apm-40332-4.10"⟩
    title := "AMD64 Architecture Programmer's Manual, Volumes 1-5"
    publisher := Vendor.amd.publisher
    revision := "40332 rev. 4.10"
    published := some ⟨2026, 7, 29⟩
    url := "https://docs.amd.com/api/khub/documents/SLs_hsYJwsu9rrIjE0rGxA/content"
    livenessProbe := some "AMD64 Architecture Programmer"
    retrieval := .verified amdAnchorCheckDate
    policy := .referenceOnly }

/-- The document a vendor's citations are written against. -/
def Vendor.document : Vendor → SourceDocument
  | .intel => intelSdm092
  | .amd => amd64Apm410

@[simp] theorem Vendor.document_publisher (v : Vendor) :
    v.document.publisher = v.publisher := by cases v <;> rfl

/-!
## Volumes

The volumes of each manual that this profile cites, as `Anchor.volume` strings.
Named rather than spelled at each citation so that a typo cannot silently
produce an anchor into a volume that does not exist: `Anchor.volume` takes a
`String`, so `Volume.intelBasic` is what makes the spelling checkable.
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
    (confirmed : Option Date := none) (page : Option Nat := none) : Citation :=
  { document := v.document
    anchor :=
      { volume := some volume, section_ := section_, heading := some heading,
        table := table, page := page }
    subjects := subjects
    locator := locator
    confirmed := confirmed }

@[simp] theorem cite_publisher (v : Vendor) (volume section_ heading : String)
    (subjects : List Name) (locator : String) (table : Option String)
    (confirmed : Option Date) (page : Option Nat) :
    (cite v volume section_ heading subjects locator table confirmed page).publisher =
      v.publisher := by
  simp [cite, Citation.publisher]

@[simp] theorem cite_subjects (v : Vendor) (volume section_ heading : String)
    (subjects : List Name) (locator : String) (table : Option String)
    (confirmed : Option Date) (page : Option Nat) :
    (cite v volume section_ heading subjects locator table confirmed page).subjects =
      subjects := rfl

end Grass.ISA.X86
