import Grass.ISA.X86.Bytes

/-!
# Decoding instruction bytes

The reader for `InsnEncoding.toBytes`, and the round-trip theorem
`docs/DECISIONS.md` 19 requires of the pair: "Every writer has a reader and
proves writer round-trip plus canonicalization for accepted inputs."

`Grass/ISA/X86/Encoding.lean` proves round-trip for the individual ModR/M, SIB
and REX *bytes*. This is the round-trip for a whole instruction, through the
byte string — the level at which a length error, a misplaced prefix or a
swallowed immediate can actually happen.

## Why the parse needs a table

Given `48 8D 05 44 33 22 11`, nothing about the bytes says where the instruction
ends. `8D` takes a ModR/M byte and no immediate; `C7` takes a ModR/M byte *and*
a four-byte immediate; `E9` takes no ModR/M and a four-byte immediate. The
length is a fact about the opcode, which is why `OpcodeSpec` holds it and why
`decodeInsn_toBytes` takes a matching table row as a premise — a decoder without
one has no way to find the next instruction, and guessing desynchronises.

`OpcodeSpec` is that fact, one row per opcode. `docs/INSTRUCTIONS.md` §6 asks
for exactly this shape — a registry with "enough metadata to dispatch by ISA,
mode, prefix/opcode space, feature set" — and for the failure mode this module
implements: "Unknown and ambiguous byte streams return structured errors."

## What this decoder covers, and what it refuses

The opcodes below are the ones this profile models, which is Spike 1's
instruction set plus what the probe corpus needs. Everything else returns
`DecodeError.unknownOpcode` rather than a guess.

That is a deliberately small table and the refusal is the point:
`DecodeError.unknownOpcode` is what an unrecognised opcode produces, because
returning *something* would let imported code be stepped with a semantics nobody
wrote -- the "default empty effect" `docs/INSTRUCTIONS.md` §1 forbids.

Scope, inherited from `RmEncoding`: default 64-bit address size, no legacy
prefix, no segment override. A `66`, `67`, `F2`, `F3` or segment byte is an
unknown opcode here, not a prefix, because the model has nowhere to put it.
-/

namespace Grass.ISA.X86

open Grass.Core Grass.Std.Logical

/-! ## What an opcode expects -/

/--
One row of the opcode table: what follows this opcode in the byte stream.

`hasModrm` and `immSize` are what make an instruction's length knowable. They
are properties of the opcode, not of the operands, which is why they live here
and not in `InsnEncoding`.
-/
structure OpcodeSpec where
  /-- Whether the opcode is in the `0F` two-byte space. -/
  escape : Bool
  /-- The primary opcode byte. -/
  opcode : Byte
  /-- Whether a ModR/M byte follows. -/
  hasModrm : Bool
  /-- How large an immediate follows the displacement, absent `REX.W`. -/
  immSize : Immediate.Size
  /-- Whether `REX.W` promotes this opcode's immediate to eight bytes.

  True only for `B8+rd`. This field exists because `(escape, opcode)` does not
  determine the immediate size in 64-bit mode, and a decoder that assumes it
  does reads four bytes where eight follow. See `immSizeFor`. -/
  immPromotedByRexW : Bool := false
  /-- What the opcode is, for diagnostics and review. Not consumed by the
  decoder. -/
  mnemonic : String
deriving DecidableEq, Repr

namespace OpcodeSpec

/--
The immediate size this opcode actually takes, given whether `REX.W` is set.

`OpcodeSpec.immSize` alone was wrong, and the failure was a stream
desynchronisation rather than a wrong field. `B8+rd` takes `imm32` normally and
`imm64` under `REX.W` -- it is `mov r64, imm64`. With the size keyed on the
opcode alone, `48 B8` followed by eight immediate bytes decoded as a six-byte
instruction, and the next `decodeInsn` began four bytes inside the immediate and
reported `unknownOpcode` on whatever it found. A reviewer produced
`48 B8 EF CD AB 89 67 45 23 01 48 89 C3`, where `ndisasm` puts the second
instruction at offset 10 and this decoder put it at 6.

That contradicted this module's own contract twice over: the header promises
`unknownOpcode` "rather than a guess", and warns that a decoder that guesses
lengths "desynchronises". It guessed.
-/
def immSizeFor (s : OpcodeSpec) (rexW : Bool) : Immediate.Size :=
  if s.immPromotedByRexW && rexW then .i64 else s.immSize

/-- Without `REX.W` the promotion never fires, so the plain size stands. -/
@[simp] theorem immSizeFor_false (s : OpcodeSpec) :
    s.immSizeFor false = s.immSize := by
  simp [immSizeFor]

/-- An opcode that is not promoted has one immediate size whatever `REX.W`
says. -/
@[simp] theorem immSizeFor_not_promoted {s : OpcodeSpec} (h : s.immPromotedByRexW = false)
    (w : Bool) : s.immSizeFor w = s.immSize := by
  simp [immSizeFor, h]

end OpcodeSpec

/-- Whether `REX.W` is set, for a prefix that may be absent.

Absent is not the same as present-and-clear anywhere else in this profile, but
for operand size it is: no prefix means the default operand size, which is what
a clear `REX.W` also means. -/
def rexWSet (rex : Option Rex) : Bool :=
  match rex with
  | some r => r.w == 1
  | Option.none => false

@[simp] theorem rexWSet_none : rexWSet Option.none = false := rfl

/-- Build the eight opcode-embedded-register rows a `+rd` opcode needs.

`50+rd` and `B8+rd` each occupy eight consecutive opcode bytes, one per
register's low three bits, and the REX bit chooses between the two halves of the
register file. Eight rows rather than a range because the table is a lookup, and
a range would need the lookup to know which opcodes are ranges. -/
def plusRegRows (base : Byte) (immSize : Immediate.Size) (mnemonic : String)
    (immPromotedByRexW : Bool := false) : List OpcodeSpec :=
  (List.range 8).map fun i =>
    { escape := false, opcode := base + BitVec.ofNat 8 i, hasModrm := false,
      immSize := immSize, immPromotedByRexW := immPromotedByRexW,
      mnemonic := mnemonic ++ "+rd" }

/--
The opcodes this profile decodes.

Spike 1's instruction set, plus the forms the probe corpus executes. Anything
absent is `unknownOpcode`, deliberately.
-/
def opcodeTable : List OpcodeSpec :=
  [ { escape := false, opcode := 0x8D, hasModrm := true, immSize := .none,
      mnemonic := "lea" },
    { escape := false, opcode := 0xFF, hasModrm := true, immSize := .none,
      mnemonic := "group5 (inc/dec/call/jmp/push r/m)" },
    { escape := false, opcode := 0xC7, hasModrm := true, immSize := .i32,
      mnemonic := "mov r/m, imm32" },
    { escape := false, opcode := 0x89, hasModrm := true, immSize := .none,
      mnemonic := "mov r/m, r" },
    { escape := false, opcode := 0x8B, hasModrm := true, immSize := .none,
      mnemonic := "mov r, r/m" },
    { escape := false, opcode := 0x85, hasModrm := true, immSize := .none,
      mnemonic := "test r/m, r" },
    { escape := false, opcode := 0x39, hasModrm := true, immSize := .none,
      mnemonic := "cmp r/m, r" },
    { escape := false, opcode := 0x01, hasModrm := true, immSize := .none,
      mnemonic := "add r/m, r" },
    { escape := false, opcode := 0x29, hasModrm := true, immSize := .none,
      mnemonic := "sub r/m, r" },
    { escape := false, opcode := 0x31, hasModrm := true, immSize := .none,
      mnemonic := "xor r/m, r" },
    { escape := false, opcode := 0x87, hasModrm := true, immSize := .none,
      mnemonic := "xchg r/m, r" },
    { escape := false, opcode := 0x81, hasModrm := true, immSize := .i32,
      mnemonic := "group1 r/m, imm32" },
    { escape := false, opcode := 0x83, hasModrm := true, immSize := .i8,
      mnemonic := "group1 r/m, imm8" },
    { escape := false, opcode := 0xE9, hasModrm := false, immSize := .i32,
      mnemonic := "jmp rel32" },
    { escape := false, opcode := 0xEB, hasModrm := false, immSize := .i8,
      mnemonic := "jmp rel8" },
    { escape := false, opcode := 0x90, hasModrm := false, immSize := .none,
      mnemonic := "nop / xchg eax, eax" },
    { escape := false, opcode := 0xB0, hasModrm := false, immSize := .i8,
      mnemonic := "mov al, imm8" },
    { escape := false, opcode := 0xB4, hasModrm := false, immSize := .i8,
      mnemonic := "mov ah, imm8" },
    { escape := true, opcode := 0x0B, hasModrm := false, immSize := .none,
      mnemonic := "ud2" },
    { escape := true, opcode := 0x84, hasModrm := false, immSize := .i32,
      mnemonic := "jz rel32" },
    { escape := true, opcode := 0x87, hasModrm := false, immSize := .i32,
      mnemonic := "ja rel32" },
    { escape := true, opcode := 0xBC, hasModrm := true, immSize := .none,
      mnemonic := "bsf r, r/m" } ]
  ++ plusRegRows 0x50 .none "push r64"
  ++ plusRegRows 0xB8 .i32 "mov r32, imm32 / r64, imm64" (immPromotedByRexW := true)

/-- The row for an opcode, if this profile has one. -/
def findSpec (escape : Bool) (opcode : Byte) : Option OpcodeSpec :=
  opcodeTable.find? fun s => s.escape == escape && s.opcode == opcode

/--
The table has no two rows for one opcode.

`docs/INSTRUCTIONS.md` §6 requires registration to prove "nonambiguity or
declare an explicitly resolved overlap". This is the nonambiguity: `findSpec`
returns the first match, so a duplicate row would make the decoder's answer
depend on table order rather than on the opcode. Note that `0x87` appears twice
legitimately — once in each opcode space — which is why the key is the pair.
-/
theorem opcodeTable_unambiguous :
    (opcodeTable.map (fun s => (s.escape, s.opcode))).Nodup := by decide

/-! ## Errors -/

/--
Why a byte string did not decode.

Structured rather than `none`, because `docs/INSTRUCTIONS.md` §6 asks for
structured errors and because "ran out of bytes" and "that opcode is not
modeled" call for different responses from an importer.
-/
inductive DecodeError where
  /-- The stream ended in the middle of an instruction. -/
  | truncated (what : String)
  /-- The opcode is not in `opcodeTable`. Every legacy prefix reaches this
  case, since `InsnEncoding` has no field to represent one. -/
  | unknownOpcode (escape : Bool) (opcode : Byte)
  /-- `rm=100` with `mod ≠ 11` requires a SIB byte and the stream had none. -/
  | missingSib
deriving DecidableEq, Repr

/-! ## The decoder -/

/-- Take one byte, or say what was expected. -/
private def takeByte (what : String) :
    ByteSeq → Except DecodeError (Byte × ByteSeq)
  | [] => .error (.truncated what)
  | b :: rest => .ok (b, rest)

/-- Take eight bytes as a little-endian 64-bit value. -/
private def takeLe64 (what : String) :
    ByteSeq → Except DecodeError (BitVec 64 × ByteSeq)
  | a :: b :: c :: d :: e :: f :: g :: h :: rest =>
      .ok (h ++ g ++ f ++ e ++ d ++ c ++ b ++ a, rest)
  | _ => .error (.truncated what)

/-- Take four bytes as a little-endian 32-bit value. -/
private def takeLe32 (what : String) :
    ByteSeq → Except DecodeError (BitVec 32 × ByteSeq)
  | a :: b :: c :: d :: rest => .ok (d ++ c ++ b ++ a, rest)
  | _ => .error (.truncated what)

/-- Take the displacement bytes the ModR/M and SIB fields promise. -/
private def takeDisp (kind : DispKind) :
    ByteSeq → Except DecodeError (Displacement × ByteSeq)
  | bs =>
    match kind with
    | .none => .ok (.none, bs)
    | .d8 => do let (b, rest) ← takeByte "disp8" bs; pure (.d8 b, rest)
    | .d32 => do let (v, rest) ← takeLe32 "disp32" bs; pure (.d32 v, rest)

/-- Take the immediate bytes the opcode promises. -/
private def takeImm (size : Immediate.Size) :
    ByteSeq → Except DecodeError (Immediate × ByteSeq)
  | bs =>
    match size with
    | .none => .ok (.none, bs)
    | .i8 => do let (b, rest) ← takeByte "imm8" bs; pure (.i8 b, rest)
    | .i32 => do let (v, rest) ← takeLe32 "imm32" bs; pure (.i32 v, rest)
    | .i64 => do let (v, rest) ← takeLe64 "imm64" bs; pure (.i64 v, rest)

/--
Decode everything after the opcode: the ModR/M byte, its SIB, the displacement
those two promise, and the immediate the opcode promises.

Split out from `decodeInsn` because it is the seam the round-trip proof follows.
The prefix-and-opcode phase has four shapes (REX or not, escaped or not); this
phase has the rest, and separating them keeps each proof about one thing.
-/
def decodeOperands (rex : Option Rex) (escape : Bool) (opcode : Byte)
    (spec : OpcodeSpec) (bs : ByteSeq) :
    Except DecodeError (InsnEncoding × ByteSeq) := do
  if spec.hasModrm then
    let (modrmByte, afterModrm) ← takeByte "ModR/M" bs
    let m := ModRm.ofByte modrmByte
    let needsSib :=
      m.rm == ModRm.rmSelectsSib && m.mod != ModRm.modRegisterDirect
    let (sib, afterSib) ←
      if needsSib then do
        let (sibByte, rest) ← takeByte "SIB" afterModrm
        pure (some (Sib.ofByte sibByte), rest)
      else pure (Option.none, afterModrm)
    let (disp, afterDisp) ← takeDisp (dispKindFor m.mod m.rm sib) afterSib
    let (imm, afterImm) ← takeImm (spec.immSizeFor (rexWSet rex)) afterDisp
    pure ({ rex := rex, escape := escape, opcode := opcode,
            modrm := some m, sib := sib, disp := disp, imm := imm },
          afterImm)
  else
    let (imm, afterImm) ← takeImm (spec.immSizeFor (rexWSet rex)) bs
    pure ({ rex := rex, escape := escape, opcode := opcode,
            modrm := Option.none, sib := Option.none, disp := .none,
            imm := imm },
          afterImm)

/--
Decode one instruction, returning it and the bytes after it.

The order mirrors `InsnEncoding.toBytes`: prefix, escape, opcode, ModR/M, SIB,
displacement, immediate. It has to, and that is the argument for reading the two
functions side by side.
-/
def decodeInsn (bs : ByteSeq) : Except DecodeError (InsnEncoding × ByteSeq) := do
  let (first, afterFirst) ← takeByte "opcode or REX prefix" bs
  -- A REX prefix is only a prefix when something follows it, and it must be the
  -- last prefix before the opcode. Since no legacy prefix is representable
  -- here, "immediately before the opcode" and "first byte" coincide.
  let (rex, afterRex) :=
    if Rex.isRexByte first then
      match Rex.ofByte? first with
      | some r => (some r, afterFirst)
      | Option.none => (Option.none, bs)
    else (Option.none, bs)
  let (maybeEscape, afterEscape) ← takeByte "opcode" afterRex
  let (escape, opcode, afterOpcode) ←
    if maybeEscape == InsnEncoding.escapeByte then do
      let (op, rest) ← takeByte "opcode after 0F escape" afterEscape
      pure (true, op, rest)
    else pure (false, maybeEscape, afterEscape)
  match findSpec escape opcode with
  | Option.none => .error (.unknownOpcode escape opcode)
  | some spec => decodeOperands rex escape opcode spec afterOpcode

/-! ## Round-trip -/

/--
This encoding agrees with the table about its own shape.

The premise `decodeInsn_toBytes` needs and `InsnEncoding` cannot express: a
record may carry a ModR/M byte for an opcode that takes none, or an `imm32` for
an opcode that takes none, and the decoder would then read a different
instruction than the writer wrote. `docs/INSTRUCTIONS.md` §3 puts this fact in
the opcode's declaration, which is where `OpcodeSpec` holds it.
-/
def MatchesSpec (i : InsnEncoding) (s : OpcodeSpec) : Prop :=
  s.escape = i.escape ∧ s.opcode = i.opcode ∧
    s.hasModrm = i.modrm.isSome ∧ s.immSizeFor (rexWSet i.rex) = i.imm.sizeOf

instance (i : InsnEncoding) (s : OpcodeSpec) : Decidable (MatchesSpec i s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Reassembling four emitted bytes recovers the value, as `takeLe32` reads
them. -/
private theorem takeLe32_le32 (what : String) (v : BitVec 32) (rest : ByteSeq) :
    takeLe32 what (le32 v ++ rest) = .ok (v, rest) := by
  simp only [le32, takeLe32, List.cons_append, List.nil_append]
  rw [split32]

/-- Eight emitted bytes read back as the value that produced them. -/
private theorem takeLe64_le64 (what : String) (v : BitVec 64) (rest : ByteSeq) :
    takeLe64 what (le64 v ++ rest) = .ok (v, rest) := by
  simp only [le64, takeLe64, List.cons_append, List.nil_append]
  rw [split64]

/-- A displacement round-trips through the bytes it emits. -/
private theorem takeDisp_toBytes (d : Displacement) (rest : ByteSeq) :
    takeDisp d.kind (d.toBytes ++ rest) = .ok (d, rest) := by
  cases d with
  | none => rfl
  | d8 v => rfl
  | d32 v =>
      simp only [Displacement.kind, Displacement.toBytes, takeDisp]
      rw [takeLe32_le32]
      rfl

/-- An immediate round-trips through the bytes it emits. -/
private theorem takeImm_toBytes (i : Immediate) (rest : ByteSeq) :
    takeImm i.sizeOf (i.toBytes ++ rest) = .ok (i, rest) := by
  cases i with
  | none => rfl
  | i8 v => rfl
  | i32 v =>
      simp only [Immediate.sizeOf, Immediate.toBytes, takeImm]
      rw [takeLe32_le32]
      rfl
  | i64 v =>
      simp only [Immediate.sizeOf, Immediate.toBytes, takeImm]
      rw [takeLe64_le64]
      rfl


/--
The operand phase inverts the operand bytes.

Lemma A of the round-trip: given that the record's own fields agree with the
opcode's row and with each other, reading the ModR/M byte, its SIB, the
displacement and the immediate recovers all four and stops in the right place.
-/
private theorem decodeOperands_bytes (rex : Option Rex) (escape : Bool)
    (opcode : Byte) (spec : OpcodeSpec) (m : ModRm) (sib : Option Sib)
    (disp : Displacement) (imm : Immediate) (rest : ByteSeq)
    (hmodrm : spec.hasModrm = true)
    (hsib : sib.isSome =
      (m.rm == ModRm.rmSelectsSib && m.mod != ModRm.modRegisterDirect))
    (hdisp : disp.kind = dispKindFor m.mod m.rm sib)
    (himm : spec.immSizeFor (rexWSet rex) = imm.sizeOf) :
    decodeOperands rex escape opcode spec
      (m.toByte :: (InsnEncoding.sibBytes sib ++
        (disp.toBytes ++ (imm.toBytes ++ rest))))
      = .ok ({ rex := rex, escape := escape, opcode := opcode,
               modrm := some m, sib := sib, disp := disp, imm := imm }, rest) := by
  simp only [decodeOperands, hmodrm, if_true, takeByte, ModRm.ofByte_toByte,
    Except.bind, bind, pure, Except.pure]
  cases sib with
  | none =>
      simp only [Option.isSome] at hsib
      simp only [InsnEncoding.sibBytes, List.nil_append, ← hsib,
        Bool.false_eq_true, if_false]
      rw [← hdisp, takeDisp_toBytes disp (imm.toBytes ++ rest), himm]
      simp only [takeImm_toBytes]
  | some sb =>
      simp only [Option.isSome] at hsib
      simp only [InsnEncoding.sibBytes, List.cons_append, List.nil_append,
        ← hsib, if_true, Sib.ofByte_toByte]
      rw [← hdisp, takeDisp_toBytes disp (imm.toBytes ++ rest), himm]
      simp only [takeImm_toBytes]

/-- The operand phase for an opcode that takes no ModR/M byte.

`hdisp` is the third conjunct of `InsnEncoding.WellFormed`: with no ModR/M byte
there is nothing for a displacement to belong to, so there must not be one. -/
private theorem decodeOperands_bytes_noModrm (rex : Option Rex) (escape : Bool)
    (opcode : Byte) (spec : OpcodeSpec) (imm : Immediate) (rest : ByteSeq)
    (hmodrm : spec.hasModrm = false)
    (himm : spec.immSizeFor (rexWSet rex) = imm.sizeOf) :
    decodeOperands rex escape opcode spec (imm.toBytes ++ rest)
      = .ok ({ rex := rex, escape := escape, opcode := opcode,
               modrm := Option.none, sib := Option.none, disp := .none,
               imm := imm }, rest) := by
  simp only [decodeOperands, hmodrm, Bool.false_eq_true, if_false, himm,
    takeImm_toBytes, Except.bind, bind]
  rfl


/-- No opcode in the table is a REX prefix byte.

Without this, a record with `rex := none` whose opcode fell in `0x40`-`0x4F`
would have its opcode eaten as a prefix, and the round-trip below would be
*false* rather than merely unproved. It holds by inspection and is checked by
`decide`, so adding such an opcode fails here rather than breaking the decoder
silently. -/
theorem no_table_opcode_is_rex :
    ∀ s ∈ opcodeTable, Rex.isRexByte s.opcode = false := by decide

/-- No single-byte opcode in the table is the `0F` escape byte -- the same
hazard one step later, where the decoder would take the opcode as an escape. -/
theorem no_plain_table_opcode_is_escape :
    ∀ s ∈ opcodeTable, s.escape = false →
      (s.opcode == InsnEncoding.escapeByte) = false := by decide


/--
A SIB byte is present exactly when the ModR/M byte calls for one.

`InsnEncoding.WellFormed` states the two directions separately -- a SIB byte
implies a ModR/M byte selecting it, and a ModR/M byte selecting one implies a
SIB byte -- because each catches a different malformed record. The decoder needs
them as one Bool equality, since that is the condition it branches on.
-/
private theorem sib_isSome_eq_needed {i : InsnEncoding} {m : ModRm}
    (hwf : i.WellFormed) (hm : i.modrm = some m) :
    i.sib.isSome =
      (m.rm == ModRm.rmSelectsSib && m.mod != ModRm.modRegisterDirect) := by
  obtain ⟨hsib, hmod, _⟩ := hwf
  obtain ⟨hneeded, _⟩ := hmod m hm
  cases hs : i.sib.isSome with
  | true =>
      obtain ⟨m', hm', hrm, hmod'⟩ := hsib hs
      rw [hm] at hm'
      cases hm'
      simp [hrm, hmod']
  | false =>
      by_cases hrm : m.rm = ModRm.rmSelectsSib
      · have hmd : m.mod = ModRm.modRegisterDirect := by
          by_cases h : m.mod = ModRm.modRegisterDirect
          · exact h
          · exact absurd (hneeded ⟨hrm, h⟩) (by simp [hs])
        simp [hmd]
      · simp [hrm]

/-- The `0F` escape byte is not a REX prefix byte.

Needed for the two-byte-opcode branches of the round-trip: with no REX prefix,
the escape byte is the first byte the decoder sees, and it must not be taken as
a prefix. -/
private theorem escapeByte_not_rex :
    Rex.isRexByte InsnEncoding.escapeByte = false := by decide

/--
**The writer's round-trip, through the bytes.**

The reader recovers exactly the instruction the writer wrote and leaves exactly
the bytes that followed it. `docs/DECISIONS.md` 19 asks this of every writer,
and the `ofByte_toByte` theorems in `Grass/ISA/X86/Encoding.lean` gave it only
for the individual ModR/M, SIB and REX *bytes* — not for the instruction's
length, the prefix's position, or the immediate.

The premises are the three facts `InsnEncoding` cannot hold on its own:

- `hfind`: this opcode is one the profile models. Nothing else is decodable, by
  design.
- `hmatch`: the record agrees with the opcode's own table row about whether a
  ModR/M byte and an immediate are present. A record carrying an `imm32` for an
  opcode that takes none would be read as a shorter instruction followed by
  garbage, and no field of `InsnEncoding` rules that out — `OpcodeSpec` is where
  `docs/INSTRUCTIONS.md` §3 puts that fact.
- `hwf`: the ModR/M and SIB bytes agree with the displacement.

`rest` is universally quantified rather than empty, which is what makes this a
statement about *streams*. An instruction whose modeled length disagreed with
its emitted length would satisfy an empty-tail version and fail here.
-/
theorem decodeInsn_toBytes {i : InsnEncoding} {s : OpcodeSpec} (rest : ByteSeq)
    (hfind : findSpec i.escape i.opcode = some s)
    (hmatch : MatchesSpec i s)
    (hwf : i.WellFormed) :
    decodeInsn (i.toBytes ++ rest) = .ok (i, rest) := by
  obtain ⟨hesc, hop, hmodrmSpec, himmSpec⟩ := hmatch
  have hmem : s ∈ opcodeTable := by
    have h := hfind
    simp only [findSpec] at h
    exact List.mem_of_find?_eq_some h
  have hnotrex : Rex.isRexByte i.opcode = false := by
    rw [← hop]; exact no_table_opcode_is_rex s hmem
  have hnotesc : i.escape = false →
      (i.opcode == InsnEncoding.escapeByte) = false := by
    intro h
    rw [← hop]
    exact no_plain_table_opcode_is_escape s hmem (hesc.trans h)
  obtain ⟨hsibWf, hmodrmWf, hdispWf⟩ := hwf
  cases i with
  | mk rex escape opcode modrm sib disp imm =>
    cases modrm with
    | some m =>
        obtain ⟨_, hdispKind⟩ := hmodrmWf m rfl
        cases rex with
        | none =>
            cases escape with
            | false =>
                simp only [InsnEncoding.toBytes, decodeInsn, List.nil_append,
                  Bool.false_eq_true, if_false,
                  List.cons_append, List.append_assoc, hnotrex, hnotesc rfl,
                  hfind, InsnEncoding.rexBytes, InsnEncoding.escapeBytes,
                  InsnEncoding.modrmBytes, Bool.false_eq_true, if_false,
                  takeByte, Except.bind, bind, pure, Except.pure]
                exact decodeOperands_bytes Option.none false opcode s m sib disp
                  imm rest (by simpa using hmodrmSpec)
                  (sib_isSome_eq_needed ⟨hsibWf, hmodrmWf, hdispWf⟩ rfl) hdispKind
                  himmSpec
            | true =>
                simp only [InsnEncoding.toBytes, decodeInsn, List.nil_append,
                  if_true, List.cons_append,
                  List.append_assoc, hfind, InsnEncoding.rexBytes, InsnEncoding.escapeBytes,
                  InsnEncoding.modrmBytes, escapeByte_not_rex, Bool.false_eq_true, if_false, if_true,
                  takeByte, Except.bind, bind, pure, Except.pure]
                exact decodeOperands_bytes Option.none true opcode s m sib disp
                  imm rest (by simpa using hmodrmSpec)
                  (sib_isSome_eq_needed ⟨hsibWf, hmodrmWf, hdispWf⟩ rfl) hdispKind
                  himmSpec
        | some r =>
            cases escape with
            | false =>
                simp only [InsnEncoding.toBytes, decodeInsn,
                  Rex.isRexByte_toByte, Rex.ofByte?_toByte, Bool.false_eq_true,
                  if_false, List.cons_append,
                  List.nil_append, List.append_assoc, hnotesc rfl, hfind, InsnEncoding.rexBytes, InsnEncoding.escapeBytes,
                  InsnEncoding.modrmBytes, Bool.false_eq_true, if_false, if_true,
                  takeByte, Except.bind, bind, pure, Except.pure]
                exact decodeOperands_bytes (some r) false opcode s m sib disp
                  imm rest (by simpa using hmodrmSpec)
                  (sib_isSome_eq_needed ⟨hsibWf, hmodrmWf, hdispWf⟩ rfl) hdispKind
                  himmSpec
            | true =>
                simp only [InsnEncoding.toBytes, decodeInsn,
                  Rex.isRexByte_toByte, Rex.ofByte?_toByte, if_true,
                  List.cons_append, List.nil_append,
                  List.append_assoc, hfind, InsnEncoding.rexBytes, InsnEncoding.escapeBytes,
                  InsnEncoding.modrmBytes, if_true,
                  takeByte, Except.bind, bind, pure, Except.pure]
                exact decodeOperands_bytes (some r) true opcode s m sib disp
                  imm rest (by simpa using hmodrmSpec)
                  (sib_isSome_eq_needed ⟨hsibWf, hmodrmWf, hdispWf⟩ rfl) hdispKind
                  himmSpec
    | none =>
        -- With no ModR/M byte there is nothing for a SIB byte or a
        -- displacement to belong to, and `WellFormed` says so.
        have hsibNone : sib = Option.none := by
          cases sib with
          | none => rfl
          | some sb => exact absurd (hsibWf rfl) (by simp)
        have hdispNone : disp = .none := by
          by_cases hd : disp = Displacement.none
          · exact hd
          · exact absurd (hdispWf hd) (by simp)
        subst hsibNone
        subst hdispNone
        cases rex with
        | none =>
            cases escape with
            | false =>
                simp only [InsnEncoding.toBytes, decodeInsn, List.nil_append,
                  Bool.false_eq_true, if_false,
                  List.cons_append, hnotrex, hnotesc rfl,
                  hfind, InsnEncoding.rexBytes, InsnEncoding.escapeBytes,
                  InsnEncoding.modrmBytes, InsnEncoding.sibBytes,
                  Displacement.toBytes,
                  Bool.false_eq_true, if_false,
                  takeByte, Except.bind, bind, pure, Except.pure]
                exact decodeOperands_bytes_noModrm Option.none false opcode s imm
                  rest (by simpa using hmodrmSpec) himmSpec
            | true =>
                simp only [InsnEncoding.toBytes, decodeInsn, List.nil_append,
                  if_true, List.cons_append,
                  hfind, InsnEncoding.rexBytes, InsnEncoding.escapeBytes,
                  InsnEncoding.modrmBytes, InsnEncoding.sibBytes,
                  Displacement.toBytes,
                  escapeByte_not_rex, Bool.false_eq_true, if_false, if_true,
                  takeByte, Except.bind, bind, pure, Except.pure]
                exact decodeOperands_bytes_noModrm Option.none true opcode s imm
                  rest (by simpa using hmodrmSpec) himmSpec
        | some r =>
            cases escape with
            | false =>
                simp only [InsnEncoding.toBytes, decodeInsn,
                  Rex.isRexByte_toByte, Rex.ofByte?_toByte, Bool.false_eq_true,
                  if_false, List.cons_append,
                  List.nil_append, hnotesc rfl, hfind, InsnEncoding.rexBytes, InsnEncoding.escapeBytes,
                  InsnEncoding.modrmBytes, InsnEncoding.sibBytes,
                  Displacement.toBytes,
                  Bool.false_eq_true, if_false, if_true,
                  takeByte, Except.bind, bind, pure, Except.pure]
                exact decodeOperands_bytes_noModrm (some r) false opcode s imm
                  rest (by simpa using hmodrmSpec) himmSpec
            | true =>
                simp only [InsnEncoding.toBytes, decodeInsn,
                  Rex.isRexByte_toByte, Rex.ofByte?_toByte, if_true,
                  List.cons_append, List.nil_append,
                  hfind, InsnEncoding.rexBytes, InsnEncoding.escapeBytes,
                  InsnEncoding.modrmBytes, InsnEncoding.sibBytes,
                  Displacement.toBytes,
                  if_true,
                  takeByte, Except.bind, bind, pure, Except.pure]
                exact decodeOperands_bytes_noModrm (some r) true opcode s imm
                  rest (by simpa using hmodrmSpec) himmSpec

end Grass.ISA.X86
