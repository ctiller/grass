import Grass.Artifact.COFF.SectionTable

/-!
# COFF relocation records

This module owns the fixed 10-byte relocation container and ordered bounded
relocation blocks. `relocationType` is intentionally an uninterpreted bitvector:
c-x86 owns the machine-specific relocation facts attached to those values.
-/

namespace Grass.Artifact.COFF

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Raw fields of one COFF relocation record. -/
structure Relocation where
  virtualAddress : BitVec 32
  symbolTableIndex : BitVec 32
  relocationType : BitVec 16
deriving DecidableEq, Repr

/-- Product shape used by the generic sequencing grammar. -/
abbrev RelocationFields := BitVec 32 × BitVec 32 × BitVec 16

/-- Forget field labels without interpreting the relocation type. -/
def Relocation.toFields (relocation : Relocation) : RelocationFields :=
  (relocation.virtualAddress, relocation.symbolTableIndex,
    relocation.relocationType)

/-- Restore a named raw relocation record. -/
def Relocation.ofFields (fields : RelocationFields) : Relocation where
  virtualAddress := fields.1
  symbolTableIndex := fields.2.1
  relocationType := fields.2.2

/-- Raw relocation records and their grammar products are a total isomorphism. -/
def relocationFieldsIsomorphism : Isomorphism RelocationFields Relocation where
  forward := Relocation.ofFields
  backward := Relocation.toFields
  backward_forward := by intro fields; rcases fields with ⟨a, b, c⟩; rfl
  forward_backward := by intro relocation; rcases relocation with ⟨a, b, c⟩; rfl

/-- Generic binary grammar for the three little-endian relocation fields. -/
def relocationFieldsFormat : Format RelocationFields :=
  .seq littleEndianU32Format fun _ =>
  .seq littleEndianU32Format fun _ =>
  littleEndianU16Format

/-- Typed language of one raw COFF relocation record. -/
def relocationFormat : Format Relocation :=
  relocationFieldsFormat.iso relocationFieldsIsomorphism

/-- Decode a relocation after the 10-byte bound is established. -/
private def readCompleteRelocation
    (input : Std.Logical.ByteArray) : ParseResult Relocation :=
  match takeLittleEndian 4 input with
  | .done virtualAddress rest =>
    match takeLittleEndian 4 rest with
    | .done symbolTableIndex rest =>
      match takeLittleEndian 2 rest with
      | .done relocationType rest => .done {
          virtualAddress, symbolTableIndex, relocationType } rest
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Parse one relocation with exact whole-record incomplete-prefix
classification and exact suffix preservation. -/
def readRelocation (input : Std.Logical.ByteArray) : ParseResult Relocation :=
  if 10 ≤ input.length then
    readCompleteRelocation input
  else
    .needMore (some (10 - input.length))

/-- `readRelocation_short` reports the exact number of missing record bytes. -/
theorem readRelocation_short {input : Std.Logical.ByteArray}
    (short : input.length < 10) :
    readRelocation input = .needMore (some (10 - input.length)) := by
  simp [readRelocation, Nat.not_le.mpr short]

/-- Serialize the canonical 10-byte raw relocation record. -/
def writeRelocation (relocation : Relocation) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) relocation.virtualAddress ++
  writeLittleEndian (count := 4) relocation.symbolTableIndex ++
  writeLittleEndian (count := 2) relocation.relocationType

/-- `length_writeRelocation` fixes canonical relocation records at 10 bytes. -/
@[simp] theorem length_writeRelocation (relocation : Relocation) :
    (writeRelocation relocation).length = 10 := by
  simp [writeRelocation, writeLittleEndian, isoWriter, writeExact]

/-- Every canonical relocation serialization derives from its typed grammar. -/
theorem writeRelocation_derives (relocation : Relocation) :
    Derives relocationFormat (writeRelocation relocation) relocation Vec.empty := by
  rcases relocation with ⟨address, symbol, kind⟩
  unfold relocationFormat
  refine @Derives.iso RelocationFields Relocation relocationFieldsFormat
    relocationFieldsIsomorphism _ Vec.empty (address, symbol, kind) ?_
  simp only [writeRelocation, Vec.append_assoc]
  unfold relocationFieldsFormat littleEndianU16Format littleEndianU32Format
  exact Derives.seqAppend
    ((writeLittleEndian_realizes 4).sound address)
    (Derives.seqAppend
      ((writeLittleEndian_realizes 4).sound symbol)
      ((writeLittleEndian_realizes 2).sound kind))

/-- `readRelocation_writeRelocation_append` is the exact prefix-preserving
canonical round trip for a relocation record. -/
@[simp] theorem readRelocation_writeRelocation_append
    (relocation : Relocation) (rest : Std.Logical.ByteArray) :
    readRelocation (writeRelocation relocation ++ rest) =
      .done relocation rest := by
  rcases relocation with ⟨address, symbol, kind⟩
  simp only [readRelocation, Vec.length_append, length_writeRelocation]
  have enough : 10 ≤ 10 + rest.length := by omega
  simp only [enough, ite_true]
  simp only [readCompleteRelocation, writeRelocation, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append]

/-- Whole-record canonical writer/reader round trip. -/
@[simp] theorem readRelocation_writeRelocation (relocation : Relocation) :
    readRelocation (writeRelocation relocation) =
      .done relocation Vec.empty := by
  simpa using readRelocation_writeRelocation_append relocation Vec.empty

/-! ## Ordered bounded relocation blocks -/

/-- Host-independent recursive serializer beneath `writeRelocations`. -/
private def writeRelocationList : List Relocation → Std.Logical.ByteArray
  | [] => Vec.empty
  | relocation :: rest => writeRelocation relocation ++ writeRelocationList rest

/-- Serialize a relocation block in table order. -/
def writeRelocations (relocations : Vec Relocation) : Std.Logical.ByteArray :=
  writeRelocationList relocations.toList

/-- Consing one relocation emits it before the remaining block. -/
@[simp] theorem writeRelocations_cons (relocation : Relocation)
    (rest : Vec Relocation) :
    writeRelocations (Vec.singleton relocation ++ rest) =
      writeRelocation relocation ++ writeRelocations rest := by
  rfl

/-- A relocation block occupies exactly 10 bytes per entry. -/
@[simp] theorem length_writeRelocations (relocations : Vec Relocation) :
    (writeRelocations relocations).length = 10 * relocations.length := by
  induction relocations using Vec.recOnCons with
  | empty => rfl
  | cons relocation rest ih =>
      rw [writeRelocations_cons, Vec.length_append,
        length_writeRelocation, ih]
      simp [Nat.mul_add]

/-- Parse exactly `count` ordered relocation records. -/
def readRelocations :
    (count : Nat) → Std.Logical.ByteArray → ParseResult (Vec Relocation)
  | 0, input => .done Vec.empty input
  | count + 1, input =>
    match readRelocation input with
    | .done relocation rest =>
      match readRelocations count rest with
      | .done relocations suffix =>
        .done (Vec.singleton relocation ++ relocations) suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

/-- Successful bounded parsing returns exactly the requested relocation count. -/
theorem readRelocations_done_length {count : Nat} {input relocations rest}
    (success : readRelocations count input = .done relocations rest) :
    relocations.length = count := by
  induction count generalizing input relocations rest with
  | zero =>
      simp only [readRelocations] at success
      injection success with relocationsEq
      rw [← relocationsEq]
      simp
  | succ count ih =>
      simp only [readRelocations] at success
      split at success <;> try contradiction
      next relocation suffix parsedRelocation =>
        split at success <;> try contradiction
        next tail final parsedTail =>
          injection success with relocationsEq restEq
          rw [← relocationsEq, Vec.length_append]
          simp only [Vec.length_singleton]
          rw [ih parsedTail]
          omega

/-- Bounded relocation blocks round-trip while preserving an arbitrary suffix. -/
@[simp] theorem readRelocations_writeRelocations_append
    (relocations : Vec Relocation) (rest : Std.Logical.ByteArray) :
    readRelocations relocations.length (writeRelocations relocations ++ rest) =
      .done relocations rest := by
  induction relocations using Vec.recOnCons generalizing rest with
  | empty =>
      change readRelocations 0 (Vec.empty ++ rest) = .done Vec.empty rest
      simp [readRelocations]
  | cons relocation tail ih =>
      rw [writeRelocations_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add, Vec.append_assoc,
        readRelocations]
      rw [readRelocation_writeRelocation_append]
      simp only
      rw [ih rest]

/-- Every serialized relocation vector derives from the matching repetition
grammar without interpreting its machine-specific type values. -/
theorem writeRelocations_derives (relocations : Vec Relocation) :
    Derives (.repeat relocations.length relocationFormat)
      (writeRelocations relocations) relocations Vec.empty := by
  induction relocations using Vec.recOnCons with
  | empty => exact Derives.repeatZero relocationFormat Vec.empty
  | cons relocation tail ih =>
      rw [writeRelocations_cons, Vec.length_append]
      simp only [Vec.length_singleton, Nat.one_add]
      exact Derives.repeatSucc
        ((writeRelocation_derives relocation).appendSuffix
          (writeRelocations tail)) ih

/-! ## Section-declared relocation blocks -/

/-- Proof-bearing relocation vector for one particular section header. -/
abbrev CheckedRelocationBlock (sectionHeader : SectionHeader) :=
  {relocations : Vec Relocation //
    relocations.length = sectionHeader.numberOfRelocations.toNat}

/-- Relocations whose count is coupled to a particular section-table entry. -/
structure RelocationBlock (sectionHeader : SectionHeader) where
  relocations : Vec Relocation
  relocationCount :
    relocations.length = sectionHeader.numberOfRelocations.toNat
deriving DecidableEq, Repr

/-- Restore the named block wrapper from a checked vector. -/
def RelocationBlock.ofChecked {sectionHeader : SectionHeader}
    (block : CheckedRelocationBlock sectionHeader) :
    RelocationBlock sectionHeader where
  relocations := block.1
  relocationCount := block.2

/-- Forget only the wrapper label, retaining the exact count proof. -/
def RelocationBlock.toChecked {sectionHeader : SectionHeader}
    (block : RelocationBlock sectionHeader) :
    CheckedRelocationBlock sectionHeader :=
  ⟨block.relocations, block.relocationCount⟩

/-- Named and subtype representations of a section's relocation block are
totally isomorphic. -/
def relocationBlockIsomorphism (sectionHeader : SectionHeader) :
    Isomorphism (CheckedRelocationBlock sectionHeader)
      (RelocationBlock sectionHeader) where
  forward := RelocationBlock.ofChecked
  backward := RelocationBlock.toChecked
  backward_forward := by intro block; rcases block with ⟨entries, count⟩; rfl
  forward_backward := by intro block; rcases block with ⟨entries, count⟩; rfl

/-- Count-refined repetition grammar for one section's relocation block. -/
def checkedRelocationBlockFormat (sectionHeader : SectionHeader) :
    Format (CheckedRelocationBlock sectionHeader) :=
  (Format.repeat sectionHeader.numberOfRelocations.toNat
    relocationFormat).refineValue
    fun relocations =>
      relocations.length = sectionHeader.numberOfRelocations.toNat

/-- Typed relocation-block language coupled to a section header. -/
def relocationBlockFormat (sectionHeader : SectionHeader) :
    Format (RelocationBlock sectionHeader) :=
  (checkedRelocationBlockFormat sectionHeader).iso
    (relocationBlockIsomorphism sectionHeader)

/-- Parse exactly the relocation block declared by `sectionHeader`, preflighting
its entire required byte extent before decoding any entry. -/
def readRelocationBlock (sectionHeader : SectionHeader)
    (input : Std.Logical.ByteArray) : ParseResult (RelocationBlock sectionHeader) :=
  let required := 10 * sectionHeader.numberOfRelocations.toNat
  if required ≤ input.length then
    match readRelocations sectionHeader.numberOfRelocations.toNat input with
    | .done relocations rest =>
      if count : relocations.length = sectionHeader.numberOfRelocations.toNat then
        .done { relocations, relocationCount := count } rest
      else
        .invalid (.malformed "relocation-block count mismatch")
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error
  else
    .needMore (some (required - input.length))

/-- A short section relocation block reports the exact whole-block deficit. -/
theorem readRelocationBlock_short (sectionHeader : SectionHeader)
    {input : Std.Logical.ByteArray}
    (short : input.length < 10 * sectionHeader.numberOfRelocations.toNat) :
    readRelocationBlock sectionHeader input =
      .needMore (some
        (10 * sectionHeader.numberOfRelocations.toNat - input.length)) := by
  simp [readRelocationBlock, Nat.not_le.mpr short]

/-- Serialize the ordered relocations in a count-coupled block. -/
def writeRelocationBlock {sectionHeader : SectionHeader}
    (block : RelocationBlock sectionHeader) : Std.Logical.ByteArray :=
  writeRelocations block.relocations

/-- A block's serialized size is exactly ten bytes times its section-declared
relocation count. -/
@[simp] theorem length_writeRelocationBlock {sectionHeader : SectionHeader}
    (block : RelocationBlock sectionHeader) :
    (writeRelocationBlock block).length =
      10 * sectionHeader.numberOfRelocations.toNat := by
  simp [writeRelocationBlock, block.relocationCount]

/-- Canonical relocation blocks round-trip with exact suffix preservation. -/
@[simp] theorem readRelocationBlock_writeRelocationBlock_append
    {sectionHeader : SectionHeader} (block : RelocationBlock sectionHeader)
    (rest : Std.Logical.ByteArray) :
    readRelocationBlock sectionHeader (writeRelocationBlock block ++ rest) =
      .done block rest := by
  rcases block with ⟨relocations, count⟩
  simp only [readRelocationBlock, writeRelocationBlock, Vec.length_append,
    length_writeRelocations]
  have enough : 10 * sectionHeader.numberOfRelocations.toNat ≤
      10 * relocations.length + rest.length := by
    simp [count]
  simp only [enough, ite_true]
  have parsed : readRelocations sectionHeader.numberOfRelocations.toNat
      (writeRelocations relocations ++ rest) = .done relocations rest := by
    simpa only [← count] using
      readRelocations_writeRelocations_append relocations rest
  rw [parsed]
  simp only [count, ↓reduceDIte]

/-- Whole-block canonical round trip. -/
@[simp] theorem readRelocationBlock_writeRelocationBlock
    {sectionHeader : SectionHeader} (block : RelocationBlock sectionHeader) :
    readRelocationBlock sectionHeader (writeRelocationBlock block) =
      .done block Vec.empty := by
  simpa using readRelocationBlock_writeRelocationBlock_append block Vec.empty

/-- Every block serialization derives from its section-count-refined grammar. -/
theorem writeRelocationBlock_derives {sectionHeader : SectionHeader}
    (block : RelocationBlock sectionHeader) :
    Derives (relocationBlockFormat sectionHeader)
      (writeRelocationBlock block) block Vec.empty := by
  rcases block with ⟨relocations, count⟩
  unfold relocationBlockFormat
  refine @Derives.iso (CheckedRelocationBlock sectionHeader)
    (RelocationBlock sectionHeader) (checkedRelocationBlockFormat sectionHeader)
    (relocationBlockIsomorphism sectionHeader) _ Vec.empty
    ⟨relocations, count⟩ ?_
  unfold checkedRelocationBlockFormat
  apply Derives.lift
  simpa only [writeRelocationBlock, count] using
    writeRelocations_derives relocations

end Grass.Artifact.COFF
