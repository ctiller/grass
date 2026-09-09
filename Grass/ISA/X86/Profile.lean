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

Intel's nine anchors retain their recorded confirmations. AMD's existing nine
subjects have been individually mapped to the official combined APM revision
4.10, containing Volume 1 revision 3.25 and Volume 3 revision 3.38. Eight AMD
anchors are confirmed on 2026-09-09. The REX layout anchor remains unconfirmed:
its source specifies required prefix placement but does not establish the
stronger misplaced-prefix behavior still present in that rule's statement.

This repairs the active ledger's dead-source locator, not every behavior or
common-basis obligation. Eight rules still use assertedPendingConfirmation;
registerWriteExtension retains weakerCommon. No native observation or Lean
proof is used as citation evidence. The historical 4.09 identity remains dead
and separate in Sources.lean. See docs/AMD_SOURCE_MIGRATION.md for revision,
page and table mappings, source-scope corrections, and regression checks.

-/

namespace Grass.ISA.X86

open Grass.Core Grass.Cite

-- Kernel decision checks traverse the detailed source locators below.
set_option maxRecDepth 2048

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
    -- Keep the weaker common guarantee. AMD's BSF/BSR entries now directly
    -- support its unchanged-destination behavior; no observation establishes
    -- a portable guarantee or turns this into CommonBasis.agreed.
    basis := .weakerCommon
      ("clears bits 63:32 on a 32-bit destination write; BSF/BSR with a zero " ++
       "source leave the destination undefined")
      ("clears bits 63:32 on a 32-bit destination write; BSF/BSR with a zero " ++
       "source leave the destination unmodified in AMD Vol. 3 rev. 3.38, which this " ++
       "rule does not rely on")
    citation := dual writeExtension
      (cite .intel Volume.intelBasic "3.4.1.1"
        "General-Purpose Registers in 64-Bit Mode" [writeExtension]
        ("Confirmed, and it states all three cases together as this rule needs. " ++
         "Under \"When in 64-bit mode, operand size determines the number of " ++
         "valid bits in the destination general-purpose register\": \"64-bit " ++
         "operands generate a 64-bit result in the destination general-purpose " ++
         "register\"; \"32-bit operands generate a 32-bit result, zero-extended " ++
         "to a 64-bit result in the destination general-purpose register\"; and " ++
         "\"8-bit and 16-bit operands generate an 8-bit or 16-bit result. The " ++
         "upper 56 bits or 48 bits (respectively) of the destination " ++
         "general-purpose register are not modified by the operation.\" That is " ++
         "exactly `writeBack` and its four preservation theorems. The section " ++
         "states none of the three carve-outs in this rule's statement, which " ++
         "is why the existing basis is not promoted by this AMD source migration.")
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdApplication "3.1.2"
        "64-Bit-Mode Registers" [writeExtension]
        "Checked in Vol. 1 publication 24592 rev. 3.25, pp. 26-28: ordinary byte/word preservation and doubleword zero-extension; Figure 3-4 shows the high-byte overlay. In Vol. 3 publication 24594 rev. 3.38, NOP p. 272 and XCHG p. 370 distinguish opcode 90 from the ModRM exchange form. BSF and BSR pp. 123-124 specify an unchanged destination for a zero source. The common rule does not strengthen Intel's undefined-destination guarantee to AMD's stronger behavior."
        (confirmed := some amdAnchorCheckDate)
        (page := some 26)) }

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
    basis := .assertedPendingConfirmation
    citation := dual rexLayout
      (cite .intel Volume.intelInstructionFormat "2.2.1"
        "REX Prefixes" [rexLayout]
        ("Confirmed. §2.2.1 opens \"REX prefixes are instruction-prefix bytes " ++
         "used in 64-bit mode\" and Table 2-4 carries the field format. The " ++
         "INC/DEC half of the statement is in §2.2.1.2, which says the sixteen " ++
         "opcodes 40H-4FH \"represent valid instructions INC or DEC\" in the " ++
         "other modes and \"the instruction prefix REX\" in 64-bit mode, with " ++
         "the single-byte forms unavailable there. The prefix-ordering half is " ++
         "not in this section and is an open obligation.")
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "1.2.7"
        "REX Prefix" [rexLayout]
        "Checked location in Vol. 3 rev. 3.38: Figure 1-3 p. 15, INC/DEC discussion p. 16, and section 1.4.4/Table 1-15 pp. 23-24 give the field layout and extensions. Page 15 requires one REX immediately before opcode/escape. It does not establish the statement's stronger ignored/stripped-effects behavior for a REX followed by a legacy prefix. That residual keeps this citation unconfirmed; canonical producers/decoder do not admit legacy prefixes."
        (page := some 14)) }

/-- A REX prefix removes the high-byte registers and reveals four low-byte
ones. -/
def byteRegisterRexInteraction : CommonRule :=
  { subject := rexByteRegisters
    statement :=
      "In an 8-bit operand encoding without a REX prefix, register numbers 4 " ++
      "through 7 denote AH, CH, DH and BH. When any REX prefix is present, " ++
      "including one with no bits set, those numbers denote SPL, BPL, SIL and " ++
      "DIL instead, and AH, CH, DH and BH are not encodable."
    basis := .assertedPendingConfirmation
    citation := dual rexByteRegisters
      (cite .intel Volume.intelBasic "3.4.1.1"
        "General-Purpose Registers in 64-Bit Mode" [rexByteRegisters]
        ("Confirmed, after correcting the anchor. This rule previously pointed " ++
         "at Vol. 2A §2.2.1.2, which only says REX prefixes \"provide an " ++
         "additional addressing capability for byte-registers that makes the " ++
         "least-significant byte of GPRs available for byte operations\" -- " ++
         "corroborating, but strictly weaker than the substitution this rule " ++
         "states. Vol. 1 §3.4.1.1 states it: \"The architecture enforces " ++
         "this limitation by changing high-byte references (AH, BH, CH, DH) to " ++
         "low byte references (BPL, SPL, DIL, SIL: the low 8 bits for RBP, RSP, " ++
         "RDI, and RSI) for instructions using a REX prefix.\" The qualifier is " ++
         "\"instructions using a REX prefix\" with no condition on which REX " ++
         "bits are set, which is what licenses this rule's claim about an " ++
         "all-zero REX. The section supplies the substitution as a set; the " ++
         "register numbering that pairs 4/5/6/7 with AH/CH/DH/BH is Table 2-2's " ++
         "reg column in Vol. 2A §2.1.5, which lists AH at 4, CH at 5, DH " ++
         "at 6 and BH at 7.")
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "1.8.1"
        "Byte-Register Addressing" [rexByteRegisters]
        "Checked Vol. 3 rev. 3.38 p. 26 with the register-direct rows of Table 1-14 p. 22. Cross-check Vol. 1 rev. 3.25 section 3.1.2 and Figures 3-3/3-4 pp. 26-28: high-byte access is unavailable with any REX; the low bytes of SP/BP/SI/DI require REX. Read register encodings 4-7 rather than assuming the printed figure's display order."
        (confirmed := some amdAnchorCheckDate)
        (page := some 26)) }

/-- The ModR/M byte is mod, reg and r/m in bit fields 7:6, 5:3 and 2:0. -/
def modRmByteLayout : CommonRule :=
  { subject := modRmLayout
    statement :=
      "The ModRM byte carries mod in bits 7:6, reg in bits 5:3 and rm in bits " ++
      "2:0. mod=11 selects a register operand for rm; the other three values " ++
      "select memory forms. The reg field is either a register number or an " ++
      "opcode extension, determined by the opcode."
    basis := .assertedPendingConfirmation
    citation := dual modRmLayout
      (cite .intel Volume.intelInstructionFormat "2.1.3"
        "ModR/M and SIB Bytes" [modRmLayout]
        ("Confirmed as the field-layout section, and it closes by directing the " ++
         "reader to §2.1.5 \"for the encodings of the ModR/M and SIB bytes\" -- " ++
         "which is the split this profile follows, with the escape rules " ++
         "anchored there instead. The section names the three fields and says " ++
         "the reg/opcode field \"specifies either a register number or three " ++
         "more bits of opcode information\". The bit ranges themselves are in " ++
         "the instruction-format figure earlier in the chapter.")
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "1.4.1"
        "ModRM Byte Format" [modRmLayout]
        "Checked Vol. 3 rev. 3.38 Figure 1-4 p. 17 and named field descriptions/Table 1-10 p. 18. Read the bit ranges and distinguish mod=11 register-direct from memory forms; reg can extend an opcode instead of naming a register."
        (table := some "Figure 1-4")
        (confirmed := some amdAnchorCheckDate)
        (page := some 17)) }

/-- The SIB byte is scale, index and base in bit fields 7:6, 5:3 and 2:0. -/
def sibByteLayout : CommonRule :=
  { subject := sibLayout
    statement :=
      "The SIB byte carries scale in bits 7:6, index in bits 5:3 and base in " ++
      "bits 2:0. The index register is scaled by 1, 2, 4 or 8 as scale is 00, " ++
      "01, 10 or 11. A SIB byte is present exactly when the ModRM rm field is " ++
      "100 and mod is not 11."
    basis := .assertedPendingConfirmation
    citation := dual sibLayout
      (cite .intel Volume.intelInstructionFormat "2.1.3"
        "ModR/M and SIB Bytes" [sibLayout]
        ("Confirmed. The same section names the SIB byte's three fields -- " ++
         "scale, index and base -- and says the \"base-plus-index and " ++
         "scale-plus-index forms\" require it. The rule that a SIB byte is " ++
         "present only for rm=100 lives in §2.1.5's tables, where sibEscape is " ++
         "anchored.")
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "1.4.2"
        "SIB Byte Format" [sibLayout]
        "Checked Vol. 3 rev. 3.38 Figure 1-5 and Table 1-11 p. 19 for fields and scale factors. SIB presence is the r/m=100 memory-form entry and note 3 of Table 1-10 p. 18; its register-direct column is different."
        (table := some "Table 1-11")
        (confirmed := some amdAnchorCheckDate)
        (page := some 19)) }

/-- `mod=00, rm=101` is RIP-relative in 64-bit mode. -/
def ripRelativeForm : CommonRule :=
  { subject := ripRelative
    statement :=
      "With default 64-bit address size in 64-bit mode, a ModRM byte " ++
      "with mod=00 and rm=101 selects " ++
      "RIP-relative addressing: the effective address is the 32-bit signed " ++
      "displacement added to the address of the next instruction. This " ++
      "encoding does not denote an absolute 32-bit displacement, which it does " ++
      "in 32-bit and compatibility modes, and it names no general-purpose " ++
      "register, so REX.B does not apply to it."
    basis := .assertedPendingConfirmation
    citation := dual ripRelative
      (cite .intel Volume.intelInstructionFormat "2.2.1.6"
        "RIP-Relative Addressing" [ripRelative]
        ("Confirmed, all three points. The section states the effective address " ++
         "is formed \"by adding displacement to the 64-bit RIP of the next " ++
         "instruction\"; that the displacement is a \"signed 32-bit\" one with " ++
         "a 2GB range; and that \"Redundant forms of 32-bit " ++
         "displacement-addressing exist in the current ModR/M and SIB " ++
         "encodings\", which is the absolute-versus-RIP distinction. Table 2-7 " ++
         "carries the exact ModR/M and SIB encodings.")
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "1.7"
        "RIP-Relative Addressing" [ripRelative]
        "Checked Vol. 3 rev. 3.38 pp. 24-26: next-instruction RIP and signed disp32; section 1.7.1/Table 1-16 encodes mod=00,r/m=101; section 1.7.2 makes REX.B irrelevant. Section 1.7.3 adds truncation/zero-extension for address-size override, outside this decoder's default-64-bit-address-size scope."
        (confirmed := some amdAnchorCheckDate)
        (page := some 24)) }

/-- `rm=100` selects a SIB byte rather than naming `rsp`. -/
def sibEscapeForm : CommonRule :=
  { subject := sibEscape
    statement :=
      "A ModRM byte with mod other than 11 and rm=100 is followed by a SIB " ++
      "byte, and does not denote the register whose number is 100. A memory " ++
      "operand based on RSP, or on R12 which shares those low three bits, is " ++
      "therefore encoded through a SIB byte naming that register as its base."
    basis := .assertedPendingConfirmation
    citation := dual sibEscape
      (cite .intel Volume.intelInstructionFormat "2.1.5"
        "Addressing-Mode Encoding of ModR/M and SIB Bytes" [sibEscape]
        ("Confirmed. Table 2-2 carries [--][--] in the rm=100 column for each " ++
         "of mod=00, mod=01 and mod=10 (as [--][--], [--][--]+disp8 and " ++
         "[--][--]+disp32), with mod=11 giving registers instead, and note 1 " ++
         "reads \"The [--][--] nomenclature means a SIB follows the ModR/M " ++
         "byte.\" The R12 half is Table 2-5 in §2.2.1.2, which pairs " ++
         "\"SIB byte required for ESP-based addressing\" with \"SIB byte also " ++
         "required for R12-based addressing.\"")
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "1.8.2"
        "Special Encodings for Registers" [sibEscape]
        "Checked Vol. 3 rev. 3.38 Table 1-17 p. 27, first row: memory-form r/m=100 requires SIB, including R12-based addressing. Table 1-10 p. 18 distinguishes the mod=11 register form, which does not consume SIB."
        (table := some "Table 1-17")
        (confirmed := some amdAnchorCheckDate)
        (page := some 27)) }

/-- `index=100` with `REX.X` clear means no index register. -/
def noIndexForm : CommonRule :=
  { subject := noIndex
    statement :=
      "A SIB byte whose index field is 100 with REX.X clear specifies no index " ++
      "register, and the scale field has no effect. Because REX.X supplies the " ++
      "high bit, index=100 with REX.X set denotes R12, which is a usable index " ++
      "register; RSP is not encodable as an index register at all."
    basis := .assertedPendingConfirmation
    citation := dual noIndex
      (cite .intel Volume.intelInstructionFormat "2.1.5"
        "Addressing-Mode Encoding of ModR/M and SIB Bytes" [noIndex]
        ("Confirmed. Table 2-3's scaled-index row labels read [EAX] [ECX] " ++
         "[EDX] [EBX] none [EBP] [ESI] [EDI], so index=100 is \"none\", and " ++
         "the same \"none\" appears in the *2, *4 and *8 blocks -- which is " ++
         "the scale-has-no-effect half. Table 2-5 in §2.2.1.2 supplies " ++
         "the 64-bit half in full: \"ESP cannot be used as an index register\", " ++
         "REX.X \"is decoded\" for this field unlike the other two special " ++
         "cases, and \"The expanded index field allows distinguishing RSP from " ++
         "R12, therefore R12 can be used as an index.\"")
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "1.8.2"
        "Special Encodings for Registers" [noIndex]
        "Checked Vol. 3 rev. 3.38 Table 1-17 p. 27, SIB index row: the REX.X extension is decoded, permitting R12 as index but not RSP. Table 1-12 and note 1 p. 20 make the absent-index contribution zero regardless of scale."
        (table := some "Table 1-17")
        (confirmed := some amdAnchorCheckDate)
        (page := some 27)) }

/-- `base=101` with `mod=00` means no base register and a 32-bit
displacement. -/
def noBaseForm : CommonRule :=
  { subject := noBase
    statement :=
      "With default 64-bit address size in 64-bit mode, a SIB byte whose " ++
      "base field is 101 in a ModRM byte with mod=00 " ++
      "specifies no base register, and a 32-bit displacement follows. With " ++
      "mod=01 or mod=10 the same base field denotes RBP, or R13 when REX.B is " ++
      "set. With no index, this is the displacement-only form. Among " ++
      "ModRM-based memory operands it is the only encoding of an " ++
      "absolute address in 64-bit mode, since mod=00 with rm=101 is " ++
      "RIP-relative. It is not the only absolute form in the instruction set: " ++
      "the direct-memory-offset MOVs take an absolute address that is not a " ++
      "ModRM operand at all, and this profile does not model them. The " ++
      "displacement is sign-extended to 64 bits, so the displacement-only form " ++
      "with no index reaches the low " ++
      "and high 2 GiB of the address space rather than an arbitrary 32-bit " ++
      "address."
    basis := .assertedPendingConfirmation
    citation := dual noBase
      (cite .intel Volume.intelInstructionFormat "2.1.5"
        "Addressing-Mode Encoding of ModR/M and SIB Bytes" [noBase]
        ("Confirmed. Table 2-3 gives base=101 as [*], and note 1 reads \"The " ++
         "[*] nomenclature means a disp32 with no base if the MOD is 00B. " ++
         "Otherwise, [*] means disp8 or disp32 + [EBP]\", tabulating mod=00 as " ++
         "[scaled index] + disp32, mod=01 as [scaled index] + disp8 + [EBP] and " ++
         "mod=10 as [scaled index] + disp32 + [EBP]. R13 follows from REX.B " ++
         "extending the base field (Table 2-4). The sign-extension claim is " ++
         "§2.2.1.3: displacements \"remain 8 bits or 32 bits and are " ++
         "sign-extended to 64bits\". The RIP-relative contrast is §2.2.1.6 " ++
         "and the direct-memory-offset carve-out is §2.2.1.4.")
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "1.8.2"
        "Special Encodings for Registers" [noBase]
        "Checked Vol. 3 rev. 3.38 Table 1-17 p. 27, final row: mod=00/SIB base=101 ignores REX.B and has no base. Table 1-13 p. 20 supplies disp32 and distinguishes mod=01/10. Section 1.5 p. 24 sign-extends displacement; Table 1-16 p. 25 identifies displacement-only addressing when index is absent. Address-size override's truncation in section 1.7.3 is outside the default-64-bit-address-size claim."
        (table := some "Table 1-17")
        (confirmed := some amdAnchorCheckDate)
        (page := some 27)) }

/--
The citation names the document this corpus registered for its vendor.

`Citation.document` accepts any `SourceDocument`, so `Citation.FullyChecked`
binds an author only if the document is one whose retrieval status this corpus
actually established. A reviewer invented a document carrying
`retrieval := .verified` and rebuilt an attack that `FullyChecked` was added to
stop. This is the missing pin: it ties a rule's two citations to
`Vendor.document`, which is `intelSdm092` and `amd64Apm410` and nothing else.
-/
def Registered (r : CommonRule) : Prop :=
  r.citation.intel.document = Vendor.intel.document ∧
    r.citation.amd.document = Vendor.amd.document

instance (r : CommonRule) : Decidable (Registered r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every rule stated above. -/
def all : List CommonRule :=
  [registerWriteExtension, rexPrefixLayout, byteRegisterRexInteraction,
   modRmByteLayout, sibByteLayout, ripRelativeForm, sibEscapeForm,
   noIndexForm, noBaseForm]

/--
**Every rule cites a registered document.**

The check that makes `Citation.FullyChecked` mean something for this profile: no
rule here cites a document this corpus has not registered and established a
retrieval status for. Without it, `FullyChecked` is satisfiable by inventing a
`SourceDocument` with `retrieval := .verified`, which a reviewer did.

It is a check rather than a construction: `CommonRule` does not carry
`Registered` as a field, so an unregistered rule is writable and merely fails
this theorem. Making it a field is the stronger form and is an open obligation.
-/
theorem all_registered : ∀ r ∈ all, Registered r := by
  intro r hr
  simp only [all, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl⟩

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
it. Its build report supplies the current declaration and citation counts.
-/

/-! ## Open citation work

Report values rather than theorems. A theorem asserting that the AMD link is
still dead would have to be deleted to fix it, which is the wrong shape for a
defect: these shrink to empty as the work is done, and
`Ledger.CitationsChecked` becomes provable at that point.
-/

/-- Sources whose recorded location does not serve them and which have no
lawful cached copy. The active AMD pin is now live; historical records remain separate. -/
def openReleaseBlockers : List SourceDocument := commonProfileLedger.releaseBlockers

/-- Anchors with unresolved confirmation. The misplaced-REX claim remains open. -/
def openAnchorConfirmations : List Citation := commonProfileLedger.unconfirmedAnchors

end Grass.ISA.X86
