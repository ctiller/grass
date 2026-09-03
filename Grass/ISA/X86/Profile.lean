import Grass.ISA.X86.Addressing
import Grass.ISA.X86.Ledger
import Grass.ISA.X86.Sources

/-!
# The common x86-64 profile, so far

The dual-cited rules behind the register, encoding and addressing models, and
the trust ledger assembled from them.

## What a subject names

`Ledger.Coherent` requires common subjects to be distinct, so a subject names a
*rule*, not a declaration: several rules constrain `decodeMem`, and collapsing
them onto that one name would mean a consumer reading the first rule got a
different answer than one reading the second. Subjects are therefore dotted
names anchored to the declaration they constrain — `decodeMem.ripRelative`,
`decodeMem.sibEscape` — and one rule owns each.

## State of these citations

Every rule below is dual-cited, and none is confirmed. Eight assert
`CommonBasis.agreed`; `registerWriteExtension` does not, because that
constructor claims both manuals state the same guarantee and the AMD manual is
unretrievable, so its carve-outs were settled on hardware instead. That is the
honest current state and the ledger reports it rather than implying otherwise:

- `Ledger.releaseBlockers` is non-empty, because the AMD APM's recorded
  retrieval location is dead and the manual is `referenceOnly`. See
  `Grass/ISA/X86/Sources.lean`.
- `Ledger.unconfirmedAnchors` is every anchor here, because none has been
  followed inside the manual from this working copy. The Intel anchors are
  section-level and written against the SDM's stable structure; the AMD anchors
  are coarser where the subsection numbering was not verifiable, and each
  locator names the heading text to search for rather than a table number,
  because captions survive revisions and numbers do not.

What *is* proved here is what should hold regardless: the ledger is coherent,
and it accounts for every rule this profile models. Confirming the anchors moves
`confirmed` from `none` to a date and changes no other line.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Cite

namespace Rules

/-! ## Subjects -/

namespace Subject

/-- The operand-size write rule. -/
def writeExtension : Name := ⟨"Grass.ISA.X86.writeBack"⟩
/-- The REX prefix byte layout. -/
def rexLayout : Name := ⟨"Grass.ISA.X86.Rex.toByte"⟩
/-- The bare `0x40` prefix and the byte registers it unlocks. -/
def rexByteRegisters : Name := ⟨"Grass.ISA.X86.ByteReg.Encodable"⟩
/-- The ModR/M byte layout. -/
def modRmLayout : Name := ⟨"Grass.ISA.X86.ModRm.toByte"⟩
/-- The SIB byte layout. -/
def sibLayout : Name := ⟨"Grass.ISA.X86.Sib.toByte"⟩
/-- `mod=00, rm=101` is RIP-relative in 64-bit mode. -/
def ripRelative : Name := ⟨"Grass.ISA.X86.decodeMem.ripRelative"⟩
/-- `rm=100` selects a SIB byte rather than naming a register. -/
def sibEscape : Name := ⟨"Grass.ISA.X86.decodeMem.sibEscape"⟩
/-- `index=100` with `REX.X` clear means no index register. -/
def noIndex : Name := ⟨"Grass.ISA.X86.decodeMem.noIndex"⟩
/-- `base=101` with `mod=00` means no base register. -/
def noBase : Name := ⟨"Grass.ISA.X86.decodeMem.noBase"⟩

end Subject

open Subject

/-! ## Rules

Each rule pairs Grass's own statement of the modeled guarantee with an anchor in
each manual. The statement is written to be checked against both anchors; it is
never a transcript of either, for the reason in `Grass/ISA/X86/Citation.lean`.
-/

/-- A dual citation whose obligations are all discharged by decision.

Every `DualCitation` below is built through this, so the publisher, subject and
well-formedness checks are uniform and a rule that fails one of them does not
elaborate. -/
private def dual (subject : Name) (intel amd : Citation)
    (hip : intel.publisher = Vendor.intel.publisher := by decide)
    (hap : amd.publisher = Vendor.amd.publisher := by decide)
    (hic : intel.covers subject = true := by decide)
    (hac : amd.covers subject = true := by decide)
    (hiw : intel.WellFormed := by decide)
    (haw : amd.WellFormed := by decide) : DualCitation subject :=
  { intel := intel, amd := amd
    intelPublisher := hip, amdPublisher := hap
    intelCovers := hic, amdCovers := hac
    intelWellFormed := hiw, amdWellFormed := haw }

/--
A 32-bit result is zero-extended to 64 bits; 8- and 16-bit results are not.

The rule `writeBack` models. See `Grass/ISA/X86/Register.lean` for why it is the
first thing this profile states.
-/
def registerWriteExtension : CommonRule :=
  { subject := writeExtension
    statement :=
      "In 64-bit mode, an instruction that writes a 32-bit general-purpose " ++
      "register destination writes bits 31:0 and clears bits 63:32. One that " ++
      "writes an 8-bit or 16-bit destination writes those bits and leaves the " ++
      "rest of the register unchanged. A 64-bit destination replaces the " ++
      "register. Three carve-outs: opcode 90 without REX.B is NOP and writes " ++
      "no register at all, so the 32-bit rule does not reach it, while the " ++
      "same exchange encoded as 87 C0 does zero-extend; a high-byte " ++
      "destination (AH, CH, DH, BH) writes bits 15:8 and preserves 7:0 as well " ++
      "as 63:16; and an instruction whose destination the architecture leaves " ++
      "undefined for some input, such as BSF or BSR with a zero source, is " ++
      "outside the rule."
    -- Not `.agreed`: `CommonBasis.agreed` asserts that both manuals state the
    -- same guarantee, and the AMD manual is currently unretrievable
    -- (`Sources.lean`). All three carve-outs named in the statement were
    -- settled on hardware instead: `Tests/ISA/X86/MachineProbes.lean` confirms
    -- each on an Intel i9-13900H, including BSF with a zero source leaving the
    -- destination entirely unwritten. That is one part from one vendor, which
    -- is why this stays `weakerCommon`: the BSF/BSR case is exactly where the
    -- vendors are reported to differ, and a single Intel measurement cannot
    -- establish what AMD guarantees.
    basis := .weakerCommon
      ("clears bits 63:32 on a 32-bit destination write; BSF/BSR with a zero " ++
       "source leave the destination undefined")
      ("clears bits 63:32 on a 32-bit destination write; BSF/BSR with a zero " ++
       "source are reported to leave the destination unmodified, which this " ++
       "rule does not rely on")
    citation := dual writeExtension
      (cite .intel Volume.intelBasic "3.4.1.1"
        "General-Purpose Registers in 64-Bit Mode" [writeExtension]
        ("Find the subsection under 'General-Purpose Registers' that discusses " ++
         "64-bit mode operand sizes. The passage states the three cases " ++
         "together: 64-bit operands, 32-bit operands zero-extending, and 8/16-bit " ++
         "operands preserving upper bits. Check that all three appear; a source " ++
         "that states only the 32-bit case does not settle the other two."))
      (cite .amd Volume.amdApplication "3.1"
        "Registers" [writeExtension]
        ("In the general-purpose register discussion of Volume 1, find the text " ++
         "on 64-bit mode operand sizes and zero-extension of 32-bit results. " ++
         "Section numbering below the chapter was not confirmed from this " ++
         "working copy; locate by the zero-extension wording, and record the " ++
         "exact subsection when confirming.")) }

/-- The REX prefix is one of the sixteen bytes `0100WRXB`. -/
def rexPrefixLayout : CommonRule :=
  { subject := rexLayout
    statement :=
      "A REX prefix is a byte whose high nibble is 0100. Its low four bits are " ++
      "W, R, X and B in that order, from bit 3 to bit 0. W promotes the operand " ++
      "size to 64 bits; R, X and B supply the high bit of the ModRM reg field, " ++
      "the SIB index field, and the ModRM rm, SIB base or opcode register field " ++
      "respectively. In 64-bit mode these sixteen byte values are prefixes and " ++
      "no longer encode the one-byte INC and DEC forms of 32-bit mode. A REX " ++
      "prefix must be the last prefix before the opcode, after every legacy " ++
      "prefix and immediately before the opcode or its 0F escape; a REX " ++
      "separated from the opcode by any other prefix is ignored, and the " ++
      "instruction then executes without the register extensions and without " ++
      "the 64-bit operand size."
    basis := .agreed
    citation := dual rexLayout
      (cite .intel Volume.intelInstructionFormat "2.2.1"
        "REX Prefixes" [rexLayout]
        ("Find the subsection on REX prefixes within the instruction-format " ++
         "chapter, and the figure captioned for the REX prefix fields showing " ++
         "the bit assignment 0100WRXB. Confirm separately the statement that " ++
         "these encodings are no longer INC/DEC in 64-bit mode."))
      (cite .amd Volume.amdInstructions "1.2.7"
        "REX Prefix" [rexLayout]
        ("In the Instruction Formats chapter of Volume 3, find the REX prefix " ++
         "subsection and its field table. Confirm the bit order W, R, X, B and " ++
         "the high-nibble value. The subsection number was not confirmed from " ++
         "this working copy; locate by heading.")) }

/-- A REX prefix removes the high-byte registers and reveals four low-byte
ones. -/
def byteRegisterRexInteraction : CommonRule :=
  { subject := rexByteRegisters
    statement :=
      "In an 8-bit operand encoding without a REX prefix, register numbers 4 " ++
      "through 7 denote AH, CH, DH and BH. When any REX prefix is present, " ++
      "including one with no bits set, those numbers denote SPL, BPL, SIL and " ++
      "DIL instead, and AH, CH, DH and BH are not encodable."
    basis := .agreed
    citation := dual rexByteRegisters
      (cite .intel Volume.intelInstructionFormat "2.2.1.2"
        "More on REX Prefix Fields" [rexByteRegisters]
        ("Within the REX prefix subsection, find the discussion of byte-register " ++
         "addressing and the table showing which 8-bit registers are reachable " ++
         "with and without REX. Confirm that a REX prefix with no bits set has " ++
         "this effect, since that is the case the model relies on."))
      (cite .amd Volume.amdInstructions "1.2.7"
        "REX Prefix" [rexByteRegisters]
        ("In the REX prefix subsection of Volume 3, find the byte-register " ++
         "table or accompanying text describing the AH/CH/DH/BH versus " ++
         "SPL/BPL/SIL/DIL selection.")) }

/-- The ModR/M byte is mod, reg and r/m in bit fields 7:6, 5:3 and 2:0. -/
def modRmByteLayout : CommonRule :=
  { subject := modRmLayout
    statement :=
      "The ModRM byte carries mod in bits 7:6, reg in bits 5:3 and rm in bits " ++
      "2:0. mod=11 selects a register operand for rm; the other three values " ++
      "select memory forms. The reg field is either a register number or an " ++
      "opcode extension, determined by the opcode."
    basis := .agreed
    citation := dual modRmLayout
      (cite .intel Volume.intelInstructionFormat "2.1.3"
        "ModR/M and SIB Bytes" [modRmLayout]
        ("This is the section that defines the field layout, not 2.1.5, which " ++
         "holds the addressing-forms tables and is where the escape rules are " ++
         "anchored. Confirm the bit ranges mod 7:6, reg 5:3, rm 2:0 and the " ++
         "statement that reg is either a register number or an opcode " ++
         "extension."))
      (cite .amd Volume.amdInstructions "1.4"
        "ModRM and SIB Bytes" [modRmLayout]
        ("In the Instruction Formats chapter of Volume 3, find the ModRM and " ++
         "SIB section and its ModRM field table. Confirm the bit ranges " ++
         "7:6, 5:3 and 2:0.")) }

/-- The SIB byte is scale, index and base in bit fields 7:6, 5:3 and 2:0. -/
def sibByteLayout : CommonRule :=
  { subject := sibLayout
    statement :=
      "The SIB byte carries scale in bits 7:6, index in bits 5:3 and base in " ++
      "bits 2:0. The index register is scaled by 1, 2, 4 or 8 as scale is 00, " ++
      "01, 10 or 11. A SIB byte is present exactly when the ModRM rm field is " ++
      "100 and mod is not 11."
    basis := .agreed
    citation := dual sibLayout
      (cite .intel Volume.intelInstructionFormat "2.1.3"
        "ModR/M and SIB Bytes" [sibLayout]
        ("The same section as the ModR/M layout. Confirm the bit ranges scale " ++
         "7:6, index 5:3, base 2:0 and the scale-factor encoding. The rule that " ++
         "a SIB byte is present only for rm=100 is in 2.1.5's tables, which is " ++
         "where sibEscape is anchored."))
      (cite .amd Volume.amdInstructions "1.4"
        "ModRM and SIB Bytes" [sibLayout]
        ("In the ModRM and SIB section of Volume 3, find the SIB field table " ++
         "and the scale-factor encoding.")) }

/-- `mod=00, rm=101` is RIP-relative in 64-bit mode. -/
def ripRelativeForm : CommonRule :=
  { subject := ripRelative
    statement :=
      "In 64-bit mode, a ModRM byte with mod=00 and rm=101 selects " ++
      "RIP-relative addressing: the effective address is the 32-bit signed " ++
      "displacement added to the address of the next instruction. This " ++
      "encoding does not denote an absolute 32-bit displacement, which it does " ++
      "in 32-bit and compatibility modes, and it names no general-purpose " ++
      "register, so REX.B does not apply to it."
    basis := .agreed
    citation := dual ripRelative
      (cite .intel Volume.intelInstructionFormat "2.2.1.6"
        "RIP-Relative Addressing" [ripRelative]
        ("Find the RIP-relative addressing subsection within the 64-bit " ++
         "instruction-format material. Confirm three separate points: that the " ++
         "form is mod=00 with rm=101, that the displacement is relative to the " ++
         "next instruction rather than the current one, and that this replaces " ++
         "the 32-bit-mode absolute-displacement meaning of the same encoding."))
      (cite .amd Volume.amdInstructions "1.7"
        "RIP-Relative Addressing" [ripRelative]
        ("In the Instruction Formats chapter of Volume 3, find the RIP-relative " ++
         "addressing section. Confirm the same three points, in particular that " ++
         "the base is the address of the following instruction.")) }

/-- `rm=100` selects a SIB byte rather than naming `rsp`. -/
def sibEscapeForm : CommonRule :=
  { subject := sibEscape
    statement :=
      "A ModRM byte with mod other than 11 and rm=100 is followed by a SIB " ++
      "byte, and does not denote the register whose number is 100. A memory " ++
      "operand based on RSP, or on R12 which shares those low three bits, is " ++
      "therefore encoded through a SIB byte naming that register as its base."
    basis := .agreed
    citation := dual sibEscape
      (cite .intel Volume.intelInstructionFormat "2.1.5"
        "Addressing-Mode Encoding of ModR/M and SIB Bytes" [sibEscape]
        ("In the ModR/M addressing-forms table, find the rm=100 rows and the " ++
         "note marking them as selecting a SIB byte. Confirm that the note " ++
         "applies for every mod value other than 11."))
      (cite .amd Volume.amdInstructions "1.4"
        "ModRM and SIB Bytes" [sibEscape]
        ("In the ModRM and SIB section of Volume 3, find the text stating when " ++
         "a SIB byte is present.")) }

/-- `index=100` with `REX.X` clear means no index register. -/
def noIndexForm : CommonRule :=
  { subject := noIndex
    statement :=
      "A SIB byte whose index field is 100 with REX.X clear specifies no index " ++
      "register, and the scale field has no effect. Because REX.X supplies the " ++
      "high bit, index=100 with REX.X set denotes R12, which is a usable index " ++
      "register; RSP is not encodable as an index register at all."
    basis := .agreed
    citation := dual noIndex
      (cite .intel Volume.intelInstructionFormat "2.1.5"
        "Addressing-Mode Encoding of ModR/M and SIB Bytes" [noIndex]
        ("In the SIB addressing-forms table, find the index=100 column and its " ++
         "'none' entry. Then confirm in the REX material that REX.X extends this " ++
         "field, which is what makes R12 reachable here while RSP is not."))
      (cite .amd Volume.amdInstructions "1.4"
        "ModRM and SIB Bytes" [noIndex]
        ("In the SIB field table of Volume 3, find the index encoding that " ++
         "specifies no index register and the accompanying REX.X note.")) }

/-- `base=101` with `mod=00` means no base register and a 32-bit
displacement. -/
def noBaseForm : CommonRule :=
  { subject := noBase
    statement :=
      "A SIB byte whose base field is 101 in a ModRM byte with mod=00 " ++
      "specifies no base register, and a 32-bit displacement follows. With " ++
      "mod=01 or mod=10 the same base field denotes RBP, or R13 when REX.B is " ++
      "set. This is the only encoding of an absolute 32-bit address in 64-bit " ++
      "mode, since mod=00 with rm=101 is RIP-relative."
    basis := .agreed
    citation := dual noBase
      (cite .intel Volume.intelInstructionFormat "2.1.5"
        "Addressing-Mode Encoding of ModR/M and SIB Bytes" [noBase]
        ("In the SIB addressing-forms table, find the base=101 rows and the " ++
         "footnote distinguishing mod=00 from mod=01 and mod=10. Confirm that " ++
         "the displacement is 32 bits in the mod=00 case."))
      (cite .amd Volume.amdInstructions "1.4"
        "ModRM and SIB Bytes" [noBase]
        ("In the SIB field table of Volume 3, find the base encoding that " ++
         "specifies no base register and its dependence on the ModRM mod " ++
         "field.")) }

/-- Every rule stated above. -/
def all : List CommonRule :=
  [registerWriteExtension, rexPrefixLayout, byteRegisterRexInteraction,
   modRmByteLayout, sibByteLayout, ripRelativeForm, sibEscapeForm,
   noIndexForm, noBaseForm]

end Rules

/-! ## The ledger -/

/--
The common x86-64 profile's trust ledger.

No refinements and no exclusions yet: everything modeled so far is in the
intersection, which is expected for byte layouts and addressing forms. The first
refinement will arrive with an instruction whose behaviour the manuals state
differently.
-/
def commonProfileLedger : Ledger :=
  { profile := ⟨"Grass.ISA.X86.common"⟩
    common := Rules.all
    refinements := []
    exclusions := [] }

/-- The ledger does not contradict itself. See `Ledger.Coherent`. -/
theorem commonProfileLedger_coherent : commonProfileLedger.Coherent := by decide

/-!
### Coverage is not proved here

There was a `commonProfileLedger_covers` theorem in this position, discharging
`Covers` against a hand-written `Rules.Subject.modeled` list. It was circular:
`modeled` and `commonProfileLedger.commonSubjects` were built from the same nine
constants in this file and were equal by `rfl`, so the theorem said
`∀ x ∈ L, x ∈ L` and could only fail if someone edited one list and not the
other. Its docstring claimed "adding a modeled rule without a citation fails
here", which was false — adding a `def` to `Addressing.lean` changed nothing.

`Ledger.lean` names that failure mode and this file committed it by a different
route. The obligation now comes from the Lean environment in
`Tests/ISA/X86/LedgerAudit.lean`, which enumerates the declarations of the
modeled modules and holds the ledger to them. Nothing in this file can shrink
it, and the honest current figure is that 6 of 73 modeled declarations carry a
citation.
-/

/-! ## Open citation work

Report values rather than theorems. A theorem asserting that the AMD link is
still dead would have to be deleted to fix it, which is the wrong shape for a
defect: these shrink to empty as the work is done, and
`Ledger.CitationsChecked` becomes provable at that point.
-/

/-- Sources whose recorded location does not serve them and which have no
lawful cached copy. Currently the AMD APM; see `Grass/ISA/X86/Sources.lean`. -/
def openReleaseBlockers : List SourceDocument := commonProfileLedger.releaseBlockers

/-- Anchors nobody has yet followed inside the manual. Currently all of them. -/
def openAnchorConfirmations : List Citation := commonProfileLedger.unconfirmedAnchors

end Grass.ISA.X86
