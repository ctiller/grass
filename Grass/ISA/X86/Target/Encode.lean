import Grass.ISA.X86.Bytes
import Grass.ISA.X86.Target.Native

/-!
# Resolved x86-64 instructions: `Instr`, `encode`, `decode`

The `Instr` inductive this module defines has every operand resolved: no
labels, no symbolic displacements waiting for a linker, only concrete
registers, immediates and byte displacements. `encode`/`decode` are the
canonical pair `Grass.Target.ISA` needs, proved to round-trip family by
family so that adding a new instruction family adds one constructor and one
proof case, not a change to the shared theorem.

## What is reused, and what is not

The REX, ModR/M and SIB byte *layouts* (`Grass.ISA.X86.Rex`/`ModRm`/`Sib`),
the register encoding (`Grass.ISA.X86.Gpr`), and the addressing model
(`Grass.ISA.X86.MemOperand`/`RmEncoding`/`encodeMem`/`decodeMem`) are proved
once in `Grass/ISA/X86/**` and reused here unchanged — they are general x86-64
facts, not shaped by any program. The opcode dispatch (`decodeInsn` in
`Grass/ISA/X86/Decode.lean`) is *not* reused: it is keyed to a fixed
`opcodeTable` scoped to one probe corpus, and extending it is not this
module's call to make. This file reads bytes itself, against its own opcode
choices, using only the byte-layout and addressing primitives above.

## Byte order

Displacements and 32/64-bit immediates are little-endian, exactly as
`Grass.ISA.X86.le32`/`le64`/`split32`/`split64` already state and prove; this
module never restates that fact, only uses it.
-/

namespace Grass.ISA.X86.Target

open Grass.Std.Logical (Byte ByteSeq)
open Grass.ISA.X86 (Rex ModRm Sib Gpr MemOperand RmEncoding
  Displacement le32 le64 split32 split64 encodeMem decodeMem decodeMem_encodeMem
  dispKindFor DispKind Scale)

/-! ## Operand vocabulary -/

/-- An ALU/MOV operand width: 32-bit (the default in 64-bit mode) or 64-bit
(`REX.W`). -/
inductive Sz where
  | w32
  | w64
deriving DecidableEq, Repr, Inhabited

/-- Whether this width sets `REX.W`. -/
def Sz.isW64 : Sz → Bool
  | .w32 => false
  | .w64 => true

/-- The six binary ALU operations this profile models, named by their
group-1 `/digit` extension (Intel SDM Vol. 2A, Table A-6): `add`=0, `or`=1,
`and`=4, `sub`=5, `xor`=6, `cmp`=7. `adc`/`sbb` (2/3) are not modeled. -/
inductive AluOp where
  | add | or_ | and_ | sub | xor_ | cmp
deriving DecidableEq, Repr, Inhabited

/-- The group-1 `/digit` extension. -/
def AluOp.digit : AluOp → BitVec 3
  | .add => 0 | .or_ => 1 | .and_ => 4 | .sub => 5 | .xor_ => 6 | .cmp => 7

/-- The dedicated `r/m, r` opcode (Intel's "MI"/"MR" form: the register
operand is written into `ModRM.reg`, the other operand into `ModRM.r/m`).
`01`=add, `09`=or, `21`=and, `29`=sub, `31`=xor, `39`=cmp. -/
def AluOp.opMR : AluOp → Byte
  | .add => 0x01 | .or_ => 0x09 | .and_ => 0x21
  | .sub => 0x29 | .xor_ => 0x31 | .cmp => 0x39

/-- The dedicated `r, r/m` opcode ("RM" form): `03`=add, `0B`=or, `23`=and,
`2B`=sub, `33`=xor, `3B`=cmp. -/
def AluOp.opRM : AluOp → Byte
  | .add => 0x03 | .or_ => 0x0B | .and_ => 0x23
  | .sub => 0x2B | .xor_ => 0x33 | .cmp => 0x3B

/-- Group-2 shift operations, named by `/digit`: `shl`=4, `shr`=5, `sar`=7. -/
inductive ShiftOp where
  | shl | shr | sar
deriving DecidableEq, Repr, Inhabited

def ShiftOp.digit : ShiftOp → BitVec 3
  | .shl => 4 | .shr => 5 | .sar => 7

/-- The sixteen condition codes of Intel SDM Vol. 1 §3.4.3 Table 3-1, in
their 4-bit encoding order (`o`=0 through `g`=15). Every `jcc`/`setcc`/`cmovcc`
in this profile is parameterized by one of these instead of being sixteen
separate constructors. -/
inductive Cond where
  | o | no | b | ae | e | ne | be | a | s | ns | p | np | l | ge | le | g
deriving DecidableEq, Repr, Inhabited

namespace Cond

/-- Every condition, in encoding order. -/
def all : List Cond :=
  [.o, .no, .b, .ae, .e, .ne, .be, .a, .s, .ns, .p, .np, .l, .ge, .le, .g]

@[simp] theorem length_all : all.length = 16 := rfl

/-- The condition's 4-bit encoding, embedded in `70+cc`, `0F 80+cc`,
`0F 90+cc` and `0F 40+cc`. -/
def code : Cond → BitVec 4
  | .o => 0 | .no => 1 | .b => 2 | .ae => 3 | .e => 4 | .ne => 5
  | .be => 6 | .a => 7 | .s => 8 | .ns => 9 | .p => 10 | .np => 11
  | .l => 12 | .ge => 13 | .le => 14 | .g => 15

/-- The condition with a given 4-bit encoding. Read out of `all`, as
`Gpr.ofIndex` reads out of `Gpr.all`: exhaustiveness of the sixteen
constructors then comes from `length_all` rather than an unreachable
default case. -/
def ofCode (c : BitVec 4) : Cond := all.getD c.toNat .o

@[simp] theorem ofCode_code (c : Cond) : ofCode c.code = c := by cases c <;> decide

end Cond

/-! ## The instruction -/

/-- One fully resolved x86-64 instruction: every operand is a concrete
register, an immediate, or a byte displacement. No label, no program-specific
name. -/
inductive Instr where
  /-- `MOV r/m, r` (`89 /r`) — `dst := src`, register-direct. -/
  | movRR (sz : Sz) (dst src : Gpr)
  /-- `MOV r32, imm32` (`B8+rd id`), zero-extending. -/
  | movRI32 (dst : Gpr) (imm : BitVec 32)
  /-- `MOV r64, imm64` (`REX.W B8+rd io`). -/
  | movRI64 (dst : Gpr) (imm : BitVec 64)
  /-- `MOVZX r, r8` or `r, r16` (`0F B6 /r` / `0F B7 /r`), register-register.
  `srcIs16` selects the source width. -/
  | movzxRR (dstSz : Sz) (dst src : Gpr) (srcIs16 : Bool)
  /-- `MOVSX r, r8` or `r, r16` (`0F BE /r` / `0F BF /r`), register-register. -/
  | movsxRR (dstSz : Sz) (dst src : Gpr) (srcIs16 : Bool)
  /-- `<op> r/m, r` (`op.opMR /r`) — `dst := dst op src`. -/
  | aluRR (op : AluOp) (sz : Sz) (dst src : Gpr)
  /-- `<op> r/m, imm32` (`81 /digit id`) — `dst := dst op imm`. -/
  | aluRI (op : AluOp) (sz : Sz) (dst : Gpr) (imm : BitVec 32)
  /-- `TEST r/m, r` (`85 /r`). -/
  | testRR (sz : Sz) (a b : Gpr)
  /-- `TEST r/m, imm32` (`F7 /0 id`). -/
  | testRI (sz : Sz) (a : Gpr) (imm : BitVec 32)
  /-- `<shift> r/m, imm8` (`C1 /digit ib`). -/
  | shiftImm (op : ShiftOp) (sz : Sz) (dst : Gpr) (imm : BitVec 8)
  /-- `IMUL r, r/m` (`0F AF /r`) — `dst := dst * src`. -/
  | imul2 (sz : Sz) (dst src : Gpr)
  /-- `INC r/m` (`FF /0`). -/
  | inc (sz : Sz) (dst : Gpr)
  /-- `DEC r/m` (`FF /1`). -/
  | dec (sz : Sz) (dst : Gpr)
  /-- `PUSH r64` (`50+rd`). -/
  | push (r : Gpr)
  /-- `POP r64` (`58+rd`). -/
  | pop (r : Gpr)
  /-- `CALL rel32` (`E8 cd`). -/
  | callRel32 (rel : BitVec 32)
  /-- `RET` (`C3`). -/
  | ret
  /-- `JMP rel32` (`E9 cd`). -/
  | jmpRel32 (rel : BitVec 32)
  /-- `JMP rel8` (`EB cb`). -/
  | jmpRel8 (rel : BitVec 8)
  /-- `Jcc rel32` (`0F 80+cc cd`). -/
  | jccRel32 (cc : Cond) (rel : BitVec 32)
  /-- `Jcc rel8` (`70+cc cb`). -/
  | jccRel8 (cc : Cond) (rel : BitVec 8)
  /-- `SYSCALL` (`0F 05`). -/
  | syscall
  /-- `UD2` (`0F 0B`). -/
  | ud2
  /-- `HLT` (`F4`). -/
  | hlt
  /-- `NOP` (`90`). -/
  | nop
  /-- `CDQ` (`99`) — sign-extend `eax` into `edx:eax`. -/
  | cdq
  /-- `CQO` (`REX.W 99`) — sign-extend `rax` into `rdx:rax`. -/
  | cqo
  /-- `DIV r/m` (`F7 /6`), unsigned. -/
  | div (sz : Sz) (src : Gpr)
  /-- `IDIV r/m` (`F7 /7`), signed. -/
  | idiv (sz : Sz) (src : Gpr)
  /-- `MUL r/m` (`F7 /4`), unsigned. -/
  | mul (sz : Sz) (src : Gpr)
  /-- `SETcc r/m8` (`0F 90+cc /r`), register-direct. -/
  | setcc (cc : Cond) (dst : Gpr)
  /-- `CMOVcc r, r/m` (`0F 40+cc /r`) — `dst := src` if `cc` holds. -/
  | cmovcc (sz : Sz) (cc : Cond) (dst src : Gpr)
  /-- `XCHG r/m, r` (`87 /r`). -/
  | xchgRR (sz : Sz) (a b : Gpr)
  /-- `MOV r, [base+disp32]` (`8B /r`).  The base form is always encoded
  with a SIB byte and a disp32, so it has one canonical representation. -/
  | movRM (sz : Sz) (dst base : Gpr) (disp : BitVec 32)
  /-- `MOV [base+disp32], imm32` (`C7 /0 id`). -/
  | movMI32 (sz : Sz) (base : Gpr) (disp imm : BitVec 32)
  /-- `LEA r64, [base+disp32]` (`REX.W 8D /r`). -/
  | leaRM (dst base : Gpr) (disp : BitVec 32)
  /-- `LEA r64, [rip+disp32]` (`REX.W 8D /r`). -/
  | leaRip (dst : Gpr) (disp : BitVec 32)
  /-- `CALL qword ptr [rip+disp32]` (`FF /2`). -/
  | callRip (disp : BitVec 32)
deriving DecidableEq, Repr, Inhabited

/-! ## Shared byte-level machinery

Everything below is proved once and used by every family below it: the
optional-REX / optional-`0F` prefix phase (`readPrefix`), the register-direct
ModR/M phase (`decModRM`), and the `[base+disp32]` / `[rip+disp32]` addressing
forms, read off `Grass.ISA.X86.encodeMem`/`decodeMem` so the `rsp`/`r12`-needs-
a-SIB-byte quirk is inherited rather than re-derived. -/

/-- A REX prefix, present exactly when one of its four bits must be set. -/
def maybeRex (w regExt idxExt rmExt : Bool) : ByteSeq :=
  if w || regExt || idxExt || rmExt then [(Rex.of w regExt idxExt rmExt).toByte] else []

/-- The register named by a 3-bit ModR/M/SIB field plus its REX extension
bit. -/
def regOfBits (ext : Bool) (bits : BitVec 3) : Gpr := Gpr.ofBits (BitVec.ofBool ext) bits

/-- `regOfBits` inverts a register's own encoding: every register is
determined by its three encoding bits and its REX extension bit. Sixteen
cases, closed by `decide`; reused by every family that reconstructs a
register from ModR/M or SIB bits. -/
theorem regOfBits_self (r : Gpr) : regOfBits r.isExtended r.encodingBits = r := by
  cases r <;> decide

/-- The `rexB` bit stored by `rmBase` agrees with the base register's
extension predicate. -/
theorem rexBitV_eq_one (r : Gpr) : (r.rexBitV == (1 : BitVec 1)) = r.isExtended := by
  cases r <;> rfl

/-- The `[base+disp32]` addressing form's encoded fields.

Always through a SIB byte (`scale=1, index=none, base=b`), never through the
shorter direct `ModRM.rm = b` form `Grass.ISA.X86.encodeMem` prefers. A real
disassembler would emit the shorter form for every base but `rsp`/`r12`
(`Grass.ISA.X86.rmSelectsSib_eq_r12` records why those two need a SIB byte at
all), but choosing the SIB form unconditionally makes this instruction's
encoding total and its round-trip proof register-independent — one byte
longer for twelve of the sixteen registers, still bytes a real CPU decodes
identically. -/
def rmBase (b : Gpr) (d : BitVec 32) : RmEncoding :=
  { mod := ModRm.modDisp32, rm := ModRm.rmSelectsSib,
    sib := some ⟨0, Sib.indexNone, b.encodingBits⟩, disp := .d32 d, rexX := 0, rexB := b.rexBitV }

/-- The `[rip+disp32]` addressing form's encoded fields: no SIB byte, `mod=00,
rm=101` (Intel SDM Vol. 2A Table 2-7). -/
def rmRip (d : BitVec 32) : RmEncoding :=
  { mod := ModRm.modNoDisplacement, rm := ModRm.rmSelectsRipRelative, sib := none,
    disp := .d32 d, rexX := 0, rexB := 0 }

/-- The REX-then-opcode prefix of a decoded instruction. -/
structure Prefix where
  rex : Option Rex
  escape : Bool
  opcode : Byte
  rest : ByteSeq
deriving Repr, DecidableEq

/-- Read the opcode/escape bytes that follow an optional REX prefix. Split out
from `readPrefix` so each phase has its own equation lemmas to unfold by
name. -/
def readAfterRex (rex : Option Rex) : ByteSeq → Option Prefix
  | [] => none
  | b1 :: rest1 =>
      if b1 = (0x0F : Byte) then
        match rest1 with
        | [] => none
        | b2 :: rest2 => some ⟨rex, true, b2, rest2⟩
      else some ⟨rex, false, b1, rest1⟩

/-- Read an optional REX prefix, the optional `0F` escape, and the opcode
byte: everything a decoded instruction carries before its operand bytes. -/
def readPrefix : ByteSeq → Option Prefix
  | [] => none
  | b0 :: rest0 =>
      match Rex.ofByte? b0 with
      | some r => readAfterRex (some r) rest0
      | none => readAfterRex none (b0 :: rest0)

/-- `readPrefix` steps to `readAfterRex` on a REX byte. -/
theorem readPrefix_cons_rex (r : Rex) (rest : ByteSeq) :
    readPrefix (r.toByte :: rest) = readAfterRex (some r) rest := by
  show (match Rex.ofByte? r.toByte with
          | some r' => readAfterRex (some r') rest
          | none => readAfterRex none (r.toByte :: rest))
        = readAfterRex (some r) rest
  rw [Rex.ofByte?_toByte]

/-- `readPrefix` steps to `readAfterRex none` on a byte that is not a REX
prefix. -/
theorem readPrefix_cons_norex {b0 : Byte} (h : Rex.isRexByte b0 = false) (rest : ByteSeq) :
    readPrefix (b0 :: rest) = readAfterRex none (b0 :: rest) := by
  show (match Rex.ofByte? b0 with
          | some r' => readAfterRex (some r') rest
          | none => readAfterRex none (b0 :: rest))
        = readAfterRex none (b0 :: rest)
  rw [Rex.ofByte?_eq_none h]

/-- `readAfterRex` on the `0F` escape byte reads one more opcode byte. -/
theorem readAfterRex_escape (rex : Option Rex) (opcode : Byte) (rest : ByteSeq) :
    readAfterRex rex ((0x0F : Byte) :: opcode :: rest) = some ⟨rex, true, opcode, rest⟩ := by
  show (if (0x0F : Byte) = (0x0F : Byte) then
          (match opcode :: rest with
            | [] => none
            | b2 :: rest2 => some (Prefix.mk rex true b2 rest2))
        else some (Prefix.mk rex false (0x0F : Byte) (opcode :: rest)))
      = some (Prefix.mk rex true opcode rest)
  rw [if_pos rfl]

/-- `readAfterRex` on any other byte reads it as the (unescaped) opcode. -/
theorem readAfterRex_noescape (rex : Option Rex) {opcode : Byte} (h : opcode ≠ (0x0F : Byte))
    (rest : ByteSeq) :
    readAfterRex rex (opcode :: rest) = some ⟨rex, false, opcode, rest⟩ := by
  show (if opcode = (0x0F : Byte) then
          (match rest with
            | [] => none
            | b2 :: rest2 => some (Prefix.mk rex true b2 rest2))
        else some (Prefix.mk rex false opcode rest))
      = some (Prefix.mk rex false opcode rest)
  rw [if_neg h]

/-- `readPrefix` inverts exactly the bytes `maybeRex` and an escape flag
produce, for any opcode that is neither a REX byte nor the escape byte
itself — which every opcode `Instr.encode` uses is, checked at each call site
by `decide`. One proof, reused by every family below. -/
theorem readPrefix_bytes (w a b c escFlag : Bool) {opcode : Byte}
    (hopc : Rex.isRexByte opcode = false) (hesc : opcode ≠ (0x0F : Byte)) (tail : ByteSeq) :
    readPrefix (maybeRex w a b c ++ (if escFlag then [(0x0F : Byte)] else []) ++ [opcode] ++ tail)
      = some ⟨if w || a || b || c then some (Rex.of w a b c) else none, escFlag, opcode, tail⟩ := by
  rcases hrex : (w || a || b || c) with _ | _ <;>
    rcases hescv : escFlag with _ | _ <;>
    subst hescv <;>
    simp only [maybeRex, hrex, Bool.false_eq_true, if_true, if_false,
      List.cons_append, List.nil_append]
  · rw [readPrefix_cons_norex hopc, readAfterRex_noescape _ hesc]
  · rw [readPrefix_cons_norex (b0 := (0x0F : Byte)) (by decide), readAfterRex_escape]
  · rw [readPrefix_cons_rex, readAfterRex_noescape _ hesc]
  · rw [readPrefix_cons_rex, readAfterRex_escape]

/-! ## Immediates -/

/-- A single immediate/displacement byte, read off the head of the stream. -/
def takeImm8 : ByteSeq → Option (BitVec 8 × ByteSeq)
  | v :: rest => some (v, rest)
  | [] => none

/-- A little-endian 32-bit immediate/displacement. -/
def takeImm32 : ByteSeq → Option (BitVec 32 × ByteSeq)
  | v0 :: v1 :: v2 :: v3 :: rest => some (v3 ++ v2 ++ v1 ++ v0, rest)
  | _ => none

/-- A little-endian 64-bit immediate. -/
def takeImm64 : ByteSeq → Option (BitVec 64 × ByteSeq)
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: rest =>
      some (v7 ++ v6 ++ v5 ++ v4 ++ v3 ++ v2 ++ v1 ++ v0, rest)
  | _ => none

theorem takeImm32_le32 (v : BitVec 32) (rest : ByteSeq) :
    takeImm32 (le32 v ++ rest) = some (v, rest) := by
  show some (BitVec.extractLsb' 24 8 v ++ BitVec.extractLsb' 16 8 v ++
      BitVec.extractLsb' 8 8 v ++ BitVec.extractLsb' 0 8 v, rest) = some (v, rest)
  rw [split32]

theorem takeImm64_le64 (v : BitVec 64) (rest : ByteSeq) :
    takeImm64 (le64 v ++ rest) = some (v, rest) := by
  show some (BitVec.extractLsb' 56 8 v ++ BitVec.extractLsb' 48 8 v ++
      BitVec.extractLsb' 40 8 v ++ BitVec.extractLsb' 32 8 v ++ BitVec.extractLsb' 24 8 v ++
      BitVec.extractLsb' 16 8 v ++ BitVec.extractLsb' 8 8 v ++ BitVec.extractLsb' 0 8 v, rest) =
      some (v, rest)
  rw [split64]

/-! ## Register-direct ModR/M (`mod = 11`) -/

/-- The `reg`/`r/m` fields of a register-direct ModR/M byte, or `none` when
`mod ≠ 11`. -/
def decModRM (bs : ByteSeq) : Option (BitVec 3 × BitVec 3 × ByteSeq) :=
  match bs with
  | [] => none
  | mByte :: rest =>
      let m := ModRm.ofByte mByte
      if m.mod = ModRm.modRegisterDirect then some (m.reg, m.rm, rest) else none

theorem decModRM_bytes (regBits rmBits : BitVec 3) (rest : ByteSeq) :
    decModRM ((ModRm.mk ModRm.modRegisterDirect regBits rmBits).toByte :: rest)
      = some (regBits, rmBits, rest) := by
  show (if (ModRm.ofByte (ModRm.mk ModRm.modRegisterDirect regBits rmBits).toByte).mod
          = ModRm.modRegisterDirect then
          some ((ModRm.ofByte (ModRm.mk ModRm.modRegisterDirect regBits rmBits).toByte).reg,
                (ModRm.ofByte (ModRm.mk ModRm.modRegisterDirect regBits rmBits).toByte).rm, rest)
        else none) = some (regBits, rmBits, rest)
  rw [ModRm.ofByte_toByte]
  rfl

/-! ## `[base+disp32]` / `[rip+disp32]` operand bytes -/

/-- Assemble a ModR/M-based instruction over a resolved `[base+disp32]` or
`[rip+disp32]` addressing form: optional REX, optional `0F` escape, opcode,
ModR/M, optional SIB, displacement, then any trailing immediate bytes. -/
def bytesMem (escapeBytes : ByteSeq) (opcode : Byte) (w : Bool) (regBits : BitVec 3)
    (regExt : Bool) (e : RmEncoding) (immBytes : ByteSeq) : ByteSeq :=
  maybeRex w regExt (e.rexX == 1) (e.rexB == 1) ++ escapeBytes ++ [opcode] ++
    [(e.modrm regBits).toByte] ++ (match e.sib with | some s => [s.toByte] | none => []) ++
    e.disp.toBytes ++ immBytes

/-- Read a `rmBase`-shaped tail: ModR/M with a mandatory SIB byte and a
mandatory disp32, the only shape `rmBase` ever produces. The base register's
three low bits come off the SIB byte; its `REX.B` extension bit is not here —
it is part of the instruction's REX prefix, read once by `readPrefix` and
combined with these bits at the call site via `Gpr.ofBits`. -/
def readMemBaseTail (bs : ByteSeq) : Option (BitVec 3 × BitVec 3 × BitVec 32 × ByteSeq) :=
  match bs with
  | mByte :: sByte :: v0 :: v1 :: v2 :: v3 :: rest =>
      let m := ModRm.ofByte mByte
      let s := Sib.ofByte sByte
      if m.mod = ModRm.modDisp32 ∧ m.rm = ModRm.rmSelectsSib ∧
          s.scale = 0 ∧ s.index = Sib.indexNone then
        some (m.reg, s.base, v3 ++ v2 ++ v1 ++ v0, rest)
      else none
  | _ => none

/-- `readMemBaseTail` inverts exactly the bytes `rmBase` and a `reg` field
produce, for any base register — the case split `rmBase` itself avoids is
avoided here too, since `rm`/`mod`/`sib` are the same concrete shape for
every base. One proof, reused by every `[base+disp32]` family below. -/
theorem readMemBaseTail_bytes (b : Gpr) (d : BitVec 32) (regBits : BitVec 3) (rest : ByteSeq) :
    readMemBaseTail (((rmBase b d).modrm regBits).toByte ::
        (Sib.toByte ⟨0, Sib.indexNone, b.encodingBits⟩ :: (le32 d ++ rest)))
      = some (regBits, b.encodingBits, d, rest) := by
  unfold readMemBaseTail
  simp [rmBase, RmEncoding.modrm, le32,
    ModRm.ofByte_toByte, Sib.ofByte_toByte, split32]

/-- Read a `rmRip`-shaped tail: ModR/M with no SIB byte and a mandatory
disp32, the only shape `rmRip` ever produces. -/
def readMemRipTail (bs : ByteSeq) : Option (BitVec 3 × BitVec 32 × ByteSeq) :=
  match bs with
  | mByte :: v0 :: v1 :: v2 :: v3 :: rest =>
      let m := ModRm.ofByte mByte
      if m.mod = ModRm.modNoDisplacement ∧ m.rm = ModRm.rmSelectsRipRelative then
        some (m.reg, v3 ++ v2 ++ v1 ++ v0, rest)
      else none
  | _ => none

theorem readMemRipTail_bytes (d : BitVec 32) (regBits : BitVec 3) (rest : ByteSeq) :
    readMemRipTail (((rmRip d).modrm regBits).toByte :: (le32 d ++ rest))
      = some (regBits, d, rest) := by
  unfold readMemRipTail
  simp [rmRip, RmEncoding.modrm, le32, ModRm.ofByte_toByte, split32]

/-! ## `encode` -/

/-- A register-direct ModR/M byte (`mod = 11`). -/
def regByte (reg rm : BitVec 3) : Byte := (ModRm.mk ModRm.modRegisterDirect reg rm).toByte

/-- Every fully resolved instruction's canonical bytes. -/
def encodeCore : Instr → ByteSeq
  | .movRR sz dst src =>
      maybeRex sz.isW64 src.isExtended false dst.isExtended ++ [0x89] ++
        [regByte src.encodingBits dst.encodingBits]
  | .movRI32 dst imm =>
      maybeRex false false false dst.isExtended ++
        [0xB8 + BitVec.setWidth 8 dst.encodingBits] ++ le32 imm
  | .movRI64 dst imm =>
      maybeRex true false false dst.isExtended ++
        [0xB8 + BitVec.setWidth 8 dst.encodingBits] ++ le64 imm
  | .movzxRR dstSz dst src srcIs16 =>
      maybeRex dstSz.isW64 dst.isExtended false src.isExtended ++
        [0x0F, if srcIs16 then 0xB7 else 0xB6] ++
        [regByte dst.encodingBits src.encodingBits]
  | .movsxRR dstSz dst src srcIs16 =>
      maybeRex dstSz.isW64 dst.isExtended false src.isExtended ++
        [0x0F, if srcIs16 then 0xBF else 0xBE] ++
        [regByte dst.encodingBits src.encodingBits]
  | .aluRR op sz dst src =>
      maybeRex sz.isW64 src.isExtended false dst.isExtended ++ [op.opMR] ++
        [regByte src.encodingBits dst.encodingBits]
  | .aluRI op sz dst imm =>
      maybeRex sz.isW64 false false dst.isExtended ++ [0x81] ++
        [regByte op.digit dst.encodingBits] ++ le32 imm
  | .testRR sz a b =>
      maybeRex sz.isW64 b.isExtended false a.isExtended ++ [0x85] ++
        [regByte b.encodingBits a.encodingBits]
  | .testRI sz a imm =>
      maybeRex sz.isW64 false false a.isExtended ++ [0xF7] ++
        [regByte 0 a.encodingBits] ++ le32 imm
  | .shiftImm op sz dst imm =>
      maybeRex sz.isW64 false false dst.isExtended ++ [0xC1] ++
        [regByte op.digit dst.encodingBits] ++ [imm]
  | .imul2 sz dst src =>
      maybeRex sz.isW64 dst.isExtended false src.isExtended ++ [0x0F, 0xAF] ++
        [regByte dst.encodingBits src.encodingBits]
  | .inc sz dst =>
      maybeRex sz.isW64 false false dst.isExtended ++ [0xFF] ++ [regByte 0 dst.encodingBits]
  | .dec sz dst =>
      maybeRex sz.isW64 false false dst.isExtended ++ [0xFF] ++ [regByte 1 dst.encodingBits]
  | .push r =>
      maybeRex false false false r.isExtended ++ [0x50 + BitVec.setWidth 8 r.encodingBits]
  | .pop r =>
      maybeRex false false false r.isExtended ++ [0x58 + BitVec.setWidth 8 r.encodingBits]
  | .callRel32 rel => [0xE8] ++ le32 rel
  | .ret => [0xC3]
  | .jmpRel32 rel => [0xE9] ++ le32 rel
  | .jmpRel8 rel => [0xEB, rel]
  | .jccRel32 cc rel => [0x0F, 0x80 + BitVec.setWidth 8 cc.code] ++ le32 rel
  | .jccRel8 cc rel => [0x70 + BitVec.setWidth 8 cc.code, rel]
  | .syscall => [0x0F, 0x05]
  | .ud2 => [0x0F, 0x0B]
  | .hlt => [0xF4]
  | .nop => [0x90]
  | .cdq => [0x99]
  | .cqo => maybeRex true false false false ++ [0x99]
  | .div sz src =>
      maybeRex sz.isW64 false false src.isExtended ++ [0xF7] ++ [regByte 6 src.encodingBits]
  | .idiv sz src =>
      maybeRex sz.isW64 false false src.isExtended ++ [0xF7] ++ [regByte 7 src.encodingBits]
  | .mul sz src =>
      maybeRex sz.isW64 false false src.isExtended ++ [0xF7] ++ [regByte 4 src.encodingBits]
  | .setcc cc dst =>
      maybeRex false false false dst.isExtended ++ [0x0F, 0x90 + BitVec.setWidth 8 cc.code] ++
        [regByte 0 dst.encodingBits]
  | .cmovcc sz cc dst src =>
      maybeRex sz.isW64 dst.isExtended false src.isExtended ++
        [0x0F, 0x40 + BitVec.setWidth 8 cc.code] ++
        [regByte dst.encodingBits src.encodingBits]
  | .xchgRR sz a b =>
      maybeRex sz.isW64 b.isExtended false a.isExtended ++ [0x87] ++
        [regByte b.encodingBits a.encodingBits]
  | .movRM sz dst base disp =>
      bytesMem [] 0x8B sz.isW64 dst.encodingBits dst.isExtended (rmBase base disp) []
  | .movMI32 sz base disp imm =>
      bytesMem [] 0xC7 sz.isW64 0 false (rmBase base disp) (le32 imm)
  | .leaRM dst base disp =>
      bytesMem [] 0x8D true dst.encodingBits dst.isExtended (rmBase base disp) []
  | .leaRip dst disp =>
      bytesMem [] 0x8D true dst.encodingBits dst.isExtended (rmRip disp) []
  | .callRip disp => bytesMem [] 0xFF false 2 false (rmRip disp) []

/-! ## `decode` -/

/-- `REX.W`, from an optional prefix; `false` when there is none. -/
def prefW (rex : Option Rex) : Bool := match rex with | some r => r.promotesTo64 | none => false
/-- `REX.R`, from an optional prefix. -/
def prefR (rex : Option Rex) : Bool := match rex with | some r => r.extendsReg | none => false
/-- `REX.B`, from an optional prefix. -/
def prefB (rex : Option Rex) : Bool := match rex with | some r => r.extendsBase | none => false

/-- The optional REX prefix that is canonical for the three named bits. -/
def canonicalRex (w r b : Bool) : Option Rex :=
  if w || r || b then some (Rex.of w r false b) else none

/-- The register a ModR/M/SIB/opcode 3-bit field names, extended by `REX.R`. -/
def regR (rex : Option Rex) (bits : BitVec 3) : Gpr := regOfBits (prefR rex) bits
/-- The register a ModR/M/SIB/opcode 3-bit field names, extended by `REX.B`. -/
def regB (rex : Option Rex) (bits : BitVec 3) : Gpr := regOfBits (prefB rex) bits

/-- `regR` on the prefix a `bytesMem`/register-direct encoder builds recovers
exactly the `reg`-field register that went in, whatever the other extension
flags are — reused so a decode proof never needs to case-split on every
register just to resolve which branch of `maybeRex`'s `if` fired. -/
theorem regR_cond (w a x c : Bool) (bits : BitVec 3) :
    regR (if w || a || x || c then some (Rex.of w a x c) else none) bits = regOfBits a bits := by
  cases w <;> cases a <;> cases x <;> cases c <;> rfl

/-- `regB` on the prefix a `bytesMem`/register-direct encoder builds recovers
exactly the `rm`/SIB-base register that went in. -/
theorem regB_cond (w a x c : Bool) (bits : BitVec 3) :
    regB (if w || a || x || c then some (Rex.of w a x c) else none) bits = regOfBits c bits := by
  cases w <;> cases a <;> cases x <;> cases c <;> rfl

/-- `prefW` on a prefix produced by `maybeRex` recovers the requested bit. -/
theorem prefW_cond (w a x c : Bool) :
    prefW (if w || a || x || c then some (Rex.of w a x c) else none) = w := by
  cases w <;> cases a <;> cases x <;> cases c <;> rfl

/-- Try the `[base+disp32]`/`[rip+disp32]` shapes against a ModR/M-first byte
stream, returning the `reg` field, whether the RIP-relative form matched, the
base-register bits (meaningless when RIP-relative), the displacement, and the
remaining bytes. Shared by every family with both addressing forms. -/
def readMemFormTail (bs : ByteSeq) : Option (BitVec 3 × Bool × BitVec 3 × BitVec 32 × ByteSeq) :=
  match bs with
  | [] => none
  | mByte :: _ =>
      let m := ModRm.ofByte mByte
      if m.mod = ModRm.modNoDisplacement ∧ m.rm = ModRm.rmSelectsRipRelative then
        match readMemRipTail bs with
        | some (regBits, disp, rest) => some (regBits, true, (0 : BitVec 3), disp, rest)
        | none => none
      else
        match readMemBaseTail bs with
        | some (regBits, baseBits, disp, rest) => some (regBits, false, baseBits, disp, rest)
        | none => none

theorem readMemFormTail_base (b : Gpr) (d : BitVec 32) (regBits : BitVec 3) (rest : ByteSeq) :
    readMemFormTail (((rmBase b d).modrm regBits).toByte ::
        (Sib.toByte ⟨0, Sib.indexNone, b.encodingBits⟩ :: (le32 d ++ rest))) =
      some (regBits, false, b.encodingBits, d, rest) := by
  have hmod : (ModRm.ofByte ((rmBase b d).modrm regBits).toByte).mod = ModRm.modDisp32 := by
    rw [ModRm.ofByte_toByte]
    rfl
  show (if (ModRm.ofByte ((rmBase b d).modrm regBits).toByte).mod = ModRm.modNoDisplacement ∧
        (ModRm.ofByte ((rmBase b d).modrm regBits).toByte).rm = ModRm.rmSelectsRipRelative then
      (match readMemRipTail (((rmBase b d).modrm regBits).toByte ::
          (Sib.toByte ⟨0, Sib.indexNone, b.encodingBits⟩ :: (le32 d ++ rest))) with
        | some (regBits', disp, rest') => some (regBits', true, (0 : BitVec 3), disp, rest')
        | none => none)
      else
      (match readMemBaseTail (((rmBase b d).modrm regBits).toByte ::
          (Sib.toByte ⟨0, Sib.indexNone, b.encodingBits⟩ :: (le32 d ++ rest))) with
        | some (regBits', baseBits, disp, rest') => some (regBits', false, baseBits, disp, rest')
        | none => none)) = some (regBits, false, b.encodingBits, d, rest)
  rw [if_neg (fun h => absurd h.1 (by rw [hmod]; decide)), readMemBaseTail_bytes]

theorem readMemFormTail_rip (d : BitVec 32) (regBits : BitVec 3) (rest : ByteSeq) :
    readMemFormTail (((rmRip d).modrm regBits).toByte :: (le32 d ++ rest)) =
      some (regBits, true, 0, d, rest) := by
  have hmod : (ModRm.ofByte ((rmRip d).modrm regBits).toByte).mod = ModRm.modNoDisplacement := by
    rw [ModRm.ofByte_toByte]
    rfl
  have hrm : (ModRm.ofByte ((rmRip d).modrm regBits).toByte).rm = ModRm.rmSelectsRipRelative := by
    rw [ModRm.ofByte_toByte]
    rfl
  show (if (ModRm.ofByte ((rmRip d).modrm regBits).toByte).mod = ModRm.modNoDisplacement ∧
        (ModRm.ofByte ((rmRip d).modrm regBits).toByte).rm = ModRm.rmSelectsRipRelative then
      (match readMemRipTail (((rmRip d).modrm regBits).toByte :: (le32 d ++ rest)) with
        | some (regBits', disp, rest') => some (regBits', true, (0 : BitVec 3), disp, rest')
        | none => none)
      else
      (match readMemBaseTail (((rmRip d).modrm regBits).toByte :: (le32 d ++ rest)) with
        | some (regBits', baseBits, disp, rest') => some (regBits', false, baseBits, disp, rest')
        | none => none)) = some (regBits, true, 0, d, rest)
  rw [if_pos (And.intro hmod hrm), readMemRipTail_bytes]

/-- `<op> r/m, r` (register-direct). -/
def aluRRDecode (op : AluOp) (sz : Sz) (p : Prefix) : Option (Instr × ByteSeq) :=
  match decModRM p.rest with
  | some (regBits, rmBits, rest) => some (.aluRR op sz (regB p.rex rmBits) (regR p.rex regBits), rest)
  | none => none

/-- Decode everything after the REX/escape/opcode prefix. -/
def decodeFromPrefix (p : Prefix) : Option (Instr × ByteSeq) :=
  let sz : Sz := if prefW p.rex then .w64 else .w32
  if p.escape then
    if p.opcode = (0x05 : Byte) then some (.syscall, p.rest)
    else if p.opcode = (0x0B : Byte) then some (.ud2, p.rest)
    else if p.opcode = (0xAF : Byte) then
      match decModRM p.rest with
      | some (regBits, rmBits, rest) => some (.imul2 sz (regR p.rex regBits) (regB p.rex rmBits), rest)
      | none => none
    else if p.opcode = (0xB6 : Byte) ∨ p.opcode = (0xB7 : Byte) then
      match decModRM p.rest with
      | some (regBits, rmBits, rest) =>
          some (.movzxRR sz (regR p.rex regBits) (regB p.rex rmBits) (p.opcode = (0xB7 : Byte)), rest)
      | none => none
    else if p.opcode = (0xBE : Byte) ∨ p.opcode = (0xBF : Byte) then
      match decModRM p.rest with
      | some (regBits, rmBits, rest) =>
          some (.movsxRR sz (regR p.rex regBits) (regB p.rex rmBits) (p.opcode = (0xBF : Byte)), rest)
      | none => none
    else if 0x40 ≤ p.opcode.toNat ∧ p.opcode.toNat ≤ 0x4F then
      match decModRM p.rest with
      | some (regBits, rmBits, rest) =>
          some (.cmovcc sz (Cond.ofCode (BitVec.ofNat 4 (p.opcode.toNat - 0x40)))
                  (regR p.rex regBits) (regB p.rex rmBits), rest)
      | none => none
    else if 0x80 ≤ p.opcode.toNat ∧ p.opcode.toNat ≤ 0x8F then
      match takeImm32 p.rest with
      | some (rel, rest) =>
          some (.jccRel32 (Cond.ofCode (BitVec.ofNat 4 (p.opcode.toNat - 0x80))) rel, rest)
      | none => none
    else if 0x90 ≤ p.opcode.toNat ∧ p.opcode.toNat ≤ 0x9F then
      match decModRM p.rest with
      | some (_, rmBits, rest) =>
          some (.setcc (Cond.ofCode (BitVec.ofNat 4 (p.opcode.toNat - 0x90))) (regB p.rex rmBits), rest)
      | none => none
    else none
  else
    if p.opcode = (0x89 : Byte) then
      match decModRM p.rest with
      | some (regBits, rmBits, rest) => some (.movRR sz (regB p.rex rmBits) (regR p.rex regBits), rest)
      | none => none
    else if p.opcode = (0x01 : Byte) then aluRRDecode .add sz p
    else if p.opcode = (0x09 : Byte) then aluRRDecode .or_ sz p
    else if p.opcode = (0x21 : Byte) then aluRRDecode .and_ sz p
    else if p.opcode = (0x29 : Byte) then aluRRDecode .sub sz p
    else if p.opcode = (0x31 : Byte) then aluRRDecode .xor_ sz p
    else if p.opcode = (0x39 : Byte) then aluRRDecode .cmp sz p
    else if p.opcode = (0x85 : Byte) then
      match decModRM p.rest with
      | some (regBits, rmBits, rest) => some (.testRR sz (regB p.rex rmBits) (regR p.rex regBits), rest)
      | none => none
    else if p.opcode = (0x87 : Byte) then
      match decModRM p.rest with
      | some (regBits, rmBits, rest) => some (.xchgRR sz (regB p.rex rmBits) (regR p.rex regBits), rest)
      | none => none
    else if p.opcode = (0x81 : Byte) then
      match decModRM p.rest with
      | some (digitBits, rmBits, rest) =>
          match takeImm32 rest with
          | some (imm, rest2) =>
              if digitBits = (0 : BitVec 3) then some (.aluRI .add sz (regB p.rex rmBits) imm, rest2)
              else if digitBits = (1 : BitVec 3) then some (.aluRI .or_ sz (regB p.rex rmBits) imm, rest2)
              else if digitBits = (4 : BitVec 3) then some (.aluRI .and_ sz (regB p.rex rmBits) imm, rest2)
              else if digitBits = (5 : BitVec 3) then some (.aluRI .sub sz (regB p.rex rmBits) imm, rest2)
              else if digitBits = (6 : BitVec 3) then some (.aluRI .xor_ sz (regB p.rex rmBits) imm, rest2)
              else if digitBits = (7 : BitVec 3) then some (.aluRI .cmp sz (regB p.rex rmBits) imm, rest2)
              else none
          | none => none
      | none => none
    else if p.opcode = (0xC1 : Byte) then
      match decModRM p.rest with
      | some (digitBits, rmBits, rest) =>
          match takeImm8 rest with
          | some (imm, rest2) =>
              if digitBits = (4 : BitVec 3) then some (.shiftImm .shl sz (regB p.rex rmBits) imm, rest2)
              else if digitBits = (5 : BitVec 3) then some (.shiftImm .shr sz (regB p.rex rmBits) imm, rest2)
              else if digitBits = (7 : BitVec 3) then some (.shiftImm .sar sz (regB p.rex rmBits) imm, rest2)
              else none
          | none => none
      | none => none
    else if p.opcode = (0xF7 : Byte) then
      match decModRM p.rest with
      | some (digitBits, rmBits, rest) =>
          if digitBits = (0 : BitVec 3) then
            match takeImm32 rest with
            | some (imm, rest2) => some (.testRI sz (regB p.rex rmBits) imm, rest2)
            | none => none
          else if digitBits = (4 : BitVec 3) then some (.mul sz (regB p.rex rmBits), rest)
          else if digitBits = (6 : BitVec 3) then some (.div sz (regB p.rex rmBits), rest)
          else if digitBits = (7 : BitVec 3) then some (.idiv sz (regB p.rex rmBits), rest)
          else none
      | none => none
    else if p.opcode = (0xFF : Byte) then
      match decModRM p.rest with
      | some (digitBits, rmBits, rest) =>
          if digitBits = (0 : BitVec 3) then some (.inc sz (regB p.rex rmBits), rest)
          else if digitBits = (1 : BitVec 3) then some (.dec sz (regB p.rex rmBits), rest)
          else none
      | none =>
          match readMemRipTail p.rest with
          | some (digitBits, disp, rest) =>
              if digitBits = (2 : BitVec 3) ∧ p.rex = none then some (.callRip disp, rest) else none
          | none => none
    else if p.opcode = (0x99 : Byte) then
      if prefW p.rex then some (.cqo, p.rest) else some (.cdq, p.rest)
    else if p.opcode = (0xC3 : Byte) then some (.ret, p.rest)
    else if p.opcode = (0xE8 : Byte) then
      match takeImm32 p.rest with
      | some (rel, rest) => some (.callRel32 rel, rest)
      | none => none
    else if p.opcode = (0xE9 : Byte) then
      match takeImm32 p.rest with
      | some (rel, rest) => some (.jmpRel32 rel, rest)
      | none => none
    else if p.opcode = (0xEB : Byte) then
      match takeImm8 p.rest with
      | some (rel, rest) => some (.jmpRel8 rel, rest)
      | none => none
    else if p.opcode = (0xF4 : Byte) then some (.hlt, p.rest)
    else if p.opcode = (0x90 : Byte) then some (.nop, p.rest)
    else if 0x50 ≤ p.opcode.toNat ∧ p.opcode.toNat ≤ 0x57 then
      some (.push (regB p.rex (BitVec.ofNat 3 (p.opcode.toNat - 0x50))), p.rest)
    else if 0x58 ≤ p.opcode.toNat ∧ p.opcode.toNat ≤ 0x5F then
      some (.pop (regB p.rex (BitVec.ofNat 3 (p.opcode.toNat - 0x58))), p.rest)
    else if 0xB8 ≤ p.opcode.toNat ∧ p.opcode.toNat ≤ 0xBF then
      if prefW p.rex then
        match takeImm64 p.rest with
        | some (imm, rest) => some (.movRI64 (regB p.rex (BitVec.ofNat 3 (p.opcode.toNat - 0xB8))) imm, rest)
        | none => none
      else
        match takeImm32 p.rest with
        | some (imm, rest) => some (.movRI32 (regB p.rex (BitVec.ofNat 3 (p.opcode.toNat - 0xB8))) imm, rest)
        | none => none
    else if 0x70 ≤ p.opcode.toNat ∧ p.opcode.toNat ≤ 0x7F then
      match takeImm8 p.rest with
      | some (rel, rest) =>
          some (.jccRel8 (Cond.ofCode (BitVec.ofNat 4 (p.opcode.toNat - 0x70))) rel, rest)
      | none => none
    else if p.opcode = (0x8B : Byte) then
      match readMemBaseTail p.rest with
      | some (regBits, baseBits, disp, rest) =>
          let dst := regR p.rex regBits
          let base := regB p.rex baseBits
          if p.rex = canonicalRex (prefW p.rex) dst.isExtended base.isExtended then
            some (.movRM sz dst base disp, rest)
          else none
      | none => none
    else if p.opcode = (0x8D : Byte) then
      match readMemFormTail p.rest with
      | some (regBits, true, _, disp, rest) =>
          let dst := regR p.rex regBits
          if p.rex = canonicalRex true dst.isExtended false then some (.leaRip dst disp, rest) else none
      | some (regBits, false, baseBits, disp, rest) =>
          let dst := regR p.rex regBits
          let base := regB p.rex baseBits
          if p.rex = canonicalRex true dst.isExtended base.isExtended then
            some (.leaRM dst base disp, rest)
          else none
      | none => none
    else if p.opcode = (0xC7 : Byte) then
      match readMemBaseTail p.rest with
      | some (digitBits, baseBits, disp, rest) =>
          if digitBits = (0 : BitVec 3) then
            match takeImm32 rest with
            | some (imm, rest2) =>
                let base := regB p.rex baseBits
                if p.rex = canonicalRex (prefW p.rex) false base.isExtended then
                  some (.movMI32 sz base disp imm, rest2)
                else none
            | none => none
          else none
      | none => none
    else none

/-- Decode one instruction, returning it and the remaining bytes. -/
def decodeInstr (bs : ByteSeq) : Option (Instr × ByteSeq) :=
  match readPrefix bs with
  | some p => decodeFromPrefix p
  | none => none

/-- Decode one instruction, returning it and the number of bytes consumed. -/
def decodeCore (bs : ByteSeq) : Option (Instr × Nat) :=
  (decodeInstr bs).map (fun ir => (ir.1, bs.length - ir.2.length))

/-! ## The public pair -/

/-- A `BitVec 8` as the `UInt8` `Grass.Target.ISA.encode` returns. -/
def toU8 (b : Byte) : UInt8 := UInt8.ofBitVec b

/-- The canonical encoding of one instruction. -/
def encode (instr : Instr) : List UInt8 := (encodeCore instr).map toU8

/-- Decode one instruction, returning it and the number of bytes consumed. -/
def decode (bs : List UInt8) : Option (Instr × Nat) := decodeCore (bs.map UInt8.toBitVec)

/-- Peel the prefix off a decode goal, for any opcode that is neither a REX
byte nor the escape byte — checked by `decide` at each call site. -/
theorem decodeInstr_prefix (w a b c escFlag : Bool) {opcode : Byte}
    (hopc : Rex.isRexByte opcode = false) (hesc : opcode ≠ (0x0F : Byte)) (tail : ByteSeq) :
    decodeInstr (maybeRex w a b c ++ (if escFlag then [(0x0F : Byte)] else []) ++ [opcode] ++ tail)
      = decodeFromPrefix ⟨if w || a || b || c then some (Rex.of w a b c) else none, escFlag,
          opcode, tail⟩ := by
  unfold decodeInstr
  rw [readPrefix_bytes w a b c escFlag hopc hesc tail]

theorem decodeInstr_prefix_noescape (w a b c : Bool) {opcode : Byte}
    (hopc : Rex.isRexByte opcode = false) (hesc : opcode ≠ (0x0F : Byte)) (tail : ByteSeq) :
    decodeInstr (maybeRex w a b c ++ [opcode] ++ tail) =
      decodeFromPrefix ⟨if w || a || b || c then some (Rex.of w a b c) else none, false, opcode, tail⟩ := by
  simpa only [Bool.false_eq_true, if_false, List.nil_append, List.append_assoc] using
    decodeInstr_prefix w a b c false hopc hesc tail

private theorem ret_correct (rest : ByteSeq) :
    decodeInstr (encodeCore .ret ++ rest) = some (Instr.ret, rest) := by
  show decodeInstr (maybeRex false false false false ++
      (if false then [(0x0F : Byte)] else []) ++ [(0xC3 : Byte)] ++ rest) = _
  rw [decodeInstr_prefix false false false false false (by decide) (by decide)]
  rfl

private theorem hlt_correct (rest : ByteSeq) :
    decodeInstr (encodeCore .hlt ++ rest) = some (Instr.hlt, rest) := by
  show decodeInstr (maybeRex false false false false ++
      (if false then [(0x0F : Byte)] else []) ++ [(0xF4 : Byte)] ++ rest) = _
  rw [decodeInstr_prefix false false false false false (by decide) (by decide)]
  rfl

private theorem nop_correct (rest : ByteSeq) :
    decodeInstr (encodeCore .nop ++ rest) = some (Instr.nop, rest) := by
  show decodeInstr (maybeRex false false false false ++
      (if false then [(0x0F : Byte)] else []) ++ [(0x90 : Byte)] ++ rest) = _
  rw [decodeInstr_prefix false false false false false (by decide) (by decide)]
  rfl

private theorem cdq_correct (rest : ByteSeq) :
    decodeInstr (encodeCore .cdq ++ rest) = some (Instr.cdq, rest) := by
  show decodeInstr (maybeRex false false false false ++
      (if false then [(0x0F : Byte)] else []) ++ [(0x99 : Byte)] ++ rest) = _
  rw [decodeInstr_prefix false false false false false (by decide) (by decide)]
  rfl

private theorem cqo_correct (rest : ByteSeq) :
    decodeInstr (encodeCore .cqo ++ rest) = some (Instr.cqo, rest) := by
  show decodeInstr (maybeRex true false false false ++
      (if false then [(0x0F : Byte)] else []) ++ [(0x99 : Byte)] ++ rest) = _
  rw [decodeInstr_prefix true false false false false (by decide) (by decide)]
  rfl

private theorem syscall_correct (rest : ByteSeq) :
    decodeInstr (encodeCore .syscall ++ rest) = some (Instr.syscall, rest) := by
  show decodeInstr (maybeRex false false false false ++
      (if true then [(0x0F : Byte)] else []) ++ [(0x05 : Byte)] ++ rest) = _
  rw [decodeInstr_prefix false false false false true (by decide) (by decide)]
  rfl

private theorem ud2_correct (rest : ByteSeq) :
    decodeInstr (encodeCore .ud2 ++ rest) = some (Instr.ud2, rest) := by
  show decodeInstr (maybeRex false false false false ++
      (if true then [(0x0F : Byte)] else []) ++ [(0x0B : Byte)] ++ rest) = _
  rw [decodeInstr_prefix false false false false true (by decide) (by decide)]
  rfl

private theorem movRR_correct (sz : Sz) (dst src : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.movRR sz dst src) ++ rest) = some (Instr.movRR sz dst src, rest) := by
  cases sz <;> cases dst <;> cases src <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem aluRR_correct (op : AluOp) (sz : Sz) (dst src : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.aluRR op sz dst src) ++ rest) =
      some (Instr.aluRR op sz dst src, rest) := by
  cases op <;> cases sz <;> cases dst <;> cases src <;> rfl

private theorem testRR_correct (sz : Sz) (a b : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.testRR sz a b) ++ rest) = some (Instr.testRR sz a b, rest) := by
  cases sz <;> cases a <;> cases b <;> rfl

private theorem xchgRR_correct (sz : Sz) (a b : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.xchgRR sz a b) ++ rest) = some (Instr.xchgRR sz a b, rest) := by
  cases sz <;> cases a <;> cases b <;> rfl

private theorem imul2_correct (sz : Sz) (dst src : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.imul2 sz dst src) ++ rest) = some (Instr.imul2 sz dst src, rest) := by
  cases sz <;> cases dst <;> cases src <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem movzxRR_correct (dstSz : Sz) (dst src : Gpr) (srcIs16 : Bool) (rest : ByteSeq) :
    decodeInstr (encodeCore (.movzxRR dstSz dst src srcIs16) ++ rest) =
      some (Instr.movzxRR dstSz dst src srcIs16, rest) := by
  cases dstSz <;> cases dst <;> cases src <;> cases srcIs16 <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem movsxRR_correct (dstSz : Sz) (dst src : Gpr) (srcIs16 : Bool) (rest : ByteSeq) :
    decodeInstr (encodeCore (.movsxRR dstSz dst src srcIs16) ++ rest) =
      some (Instr.movsxRR dstSz dst src srcIs16, rest) := by
  cases dstSz <;> cases dst <;> cases src <;> cases srcIs16 <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem setcc_correct (cc : Cond) (dst : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.setcc cc dst) ++ rest) = some (Instr.setcc cc dst, rest) := by
  cases cc <;> cases dst <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem cmovcc_correct (sz : Sz) (cc : Cond) (dst src : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.cmovcc sz cc dst src) ++ rest) =
      some (Instr.cmovcc sz cc dst src, rest) := by
  cases sz <;> cases cc <;> cases dst <;> cases src <;> rfl

private theorem inc_correct (sz : Sz) (dst : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.inc sz dst) ++ rest) = some (Instr.inc sz dst, rest) := by
  cases sz <;> cases dst <;> rfl

private theorem dec_correct (sz : Sz) (dst : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.dec sz dst) ++ rest) = some (Instr.dec sz dst, rest) := by
  cases sz <;> cases dst <;> rfl

private theorem div_correct (sz : Sz) (src : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.div sz src) ++ rest) = some (Instr.div sz src, rest) := by
  cases sz <;> cases src <;> rfl

private theorem idiv_correct (sz : Sz) (src : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.idiv sz src) ++ rest) = some (Instr.idiv sz src, rest) := by
  cases sz <;> cases src <;> rfl

private theorem mul_correct (sz : Sz) (src : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.mul sz src) ++ rest) = some (Instr.mul sz src, rest) := by
  cases sz <;> cases src <;> rfl

private theorem push_correct (r : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.push r) ++ rest) = some (Instr.push r, rest) := by
  cases r <;> rfl

private theorem pop_correct (r : Gpr) (rest : ByteSeq) :
    decodeInstr (encodeCore (.pop r) ++ rest) = some (Instr.pop r, rest) := by
  cases r <;> rfl

private theorem shiftImm_correct (op : ShiftOp) (sz : Sz) (dst : Gpr) (imm : BitVec 8)
    (rest : ByteSeq) :
    decodeInstr (encodeCore (.shiftImm op sz dst imm) ++ rest) =
      some (Instr.shiftImm op sz dst imm, rest) := by
  cases op <;> cases sz <;> cases dst <;> rfl

private theorem jmpRel8_correct (rel : BitVec 8) (rest : ByteSeq) :
    decodeInstr (encodeCore (.jmpRel8 rel) ++ rest) = some (Instr.jmpRel8 rel, rest) := by
  rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
private theorem jccRel8_correct (cc : Cond) (rel : BitVec 8) (rest : ByteSeq) :
    decodeInstr (encodeCore (.jccRel8 cc rel) ++ rest) = some (Instr.jccRel8 cc rel, rest) := by
  cases cc <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem movRI32_dispatch (dst : Gpr) (imm : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.movRI32 dst imm) ++ rest) =
      (takeImm32 (le32 imm ++ rest)).map (fun p => (Instr.movRI32 dst p.1, p.2)) := by
  cases dst <;> rfl

private theorem movRI32_correct (dst : Gpr) (imm : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.movRI32 dst imm) ++ rest) = some (Instr.movRI32 dst imm, rest) := by
  rw [movRI32_dispatch, takeImm32_le32]; rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem movRI64_dispatch (dst : Gpr) (imm : BitVec 64) (rest : ByteSeq) :
    decodeInstr (encodeCore (.movRI64 dst imm) ++ rest) =
      (takeImm64 (le64 imm ++ rest)).map (fun p => (Instr.movRI64 dst p.1, p.2)) := by
  cases dst <;> rfl

private theorem movRI64_correct (dst : Gpr) (imm : BitVec 64) (rest : ByteSeq) :
    decodeInstr (encodeCore (.movRI64 dst imm) ++ rest) = some (Instr.movRI64 dst imm, rest) := by
  rw [movRI64_dispatch, takeImm64_le64]; rfl

private theorem callRel32_correct (rel : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.callRel32 rel) ++ rest) = some (Instr.callRel32 rel, rest) := by
  rw [show decodeInstr (encodeCore (.callRel32 rel) ++ rest) =
      (takeImm32 (le32 rel ++ rest)).map (fun p => (Instr.callRel32 p.1, p.2)) from rfl,
    takeImm32_le32]; rfl

private theorem jmpRel32_correct (rel : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.jmpRel32 rel) ++ rest) = some (Instr.jmpRel32 rel, rest) := by
  rw [show decodeInstr (encodeCore (.jmpRel32 rel) ++ rest) =
      (takeImm32 (le32 rel ++ rest)).map (fun p => (Instr.jmpRel32 p.1, p.2)) from rfl,
    takeImm32_le32]; rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem jccRel32_dispatch (cc : Cond) (rel : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.jccRel32 cc rel) ++ rest) =
      (takeImm32 (le32 rel ++ rest)).map (fun p => (Instr.jccRel32 cc p.1, p.2)) := by
  cases cc <;> rfl

private theorem jccRel32_correct (cc : Cond) (rel : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.jccRel32 cc rel) ++ rest) = some (Instr.jccRel32 cc rel, rest) := by
  rw [jccRel32_dispatch, takeImm32_le32]; rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem testRI_dispatch (sz : Sz) (a : Gpr) (imm : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.testRI sz a imm) ++ rest) =
      (takeImm32 (le32 imm ++ rest)).map (fun p => (Instr.testRI sz a p.1, p.2)) := by
  cases sz <;> cases a <;> rfl

private theorem testRI_correct (sz : Sz) (a : Gpr) (imm : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.testRI sz a imm) ++ rest) = some (Instr.testRI sz a imm, rest) := by
  rw [testRI_dispatch, takeImm32_le32]; rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem aluRI_dispatch (op : AluOp) (sz : Sz) (dst : Gpr) (imm : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.aluRI op sz dst imm) ++ rest) =
      (takeImm32 (le32 imm ++ rest)).map (fun p => (Instr.aluRI op sz dst p.1, p.2)) := by
  cases op <;> cases sz <;> cases dst <;> rfl

private theorem aluRI_correct (op : AluOp) (sz : Sz) (dst : Gpr) (imm : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.aluRI op sz dst imm) ++ rest) = some (Instr.aluRI op sz dst imm, rest) := by
  rw [aluRI_dispatch, takeImm32_le32]; rfl

/-! ## Canonical memory-operand round trips -/

theorem Sz.ite_isW64 (sz : Sz) : (if sz.isW64 then Sz.w64 else Sz.w32) = sz := by
  cases sz <;> rfl

theorem decModRM_rmBase_none (b : Gpr) (d : BitVec 32) (regBits : BitVec 3) (rest : ByteSeq) :
    decModRM (((rmBase b d).modrm regBits).toByte ::
        (Sib.toByte ⟨0, Sib.indexNone, b.encodingBits⟩ :: (le32 d ++ rest))) = none := by
  unfold decModRM
  simp [rmBase, RmEncoding.modrm, ModRm.ofByte_toByte, ModRm.modDisp32, ModRm.modRegisterDirect]

theorem decModRM_rmRip_none (d : BitVec 32) (regBits : BitVec 3) (rest : ByteSeq) :
    decModRM (((rmRip d).modrm regBits).toByte :: (le32 d ++ rest)) = none := by
  unfold decModRM
  simp [rmRip, RmEncoding.modrm, ModRm.ofByte_toByte, ModRm.modNoDisplacement, ModRm.modRegisterDirect]

theorem decodeFromPrefix_8B (rex : Option Rex) (tail : ByteSeq) :
    decodeFromPrefix ⟨rex, false, (0x8B : Byte), tail⟩ =
      match readMemBaseTail tail with
      | some (regBits, baseBits, disp, rest) =>
          let dst := regR rex regBits
          let base := regB rex baseBits
          if rex = canonicalRex (prefW rex) dst.isExtended base.isExtended then
            some (.movRM (if prefW rex then .w64 else .w32) dst base disp, rest)
          else none
      | none => none := rfl

theorem decodeFromPrefix_8D (rex : Option Rex) (tail : ByteSeq) :
    decodeFromPrefix ⟨rex, false, (0x8D : Byte), tail⟩ =
      match readMemFormTail tail with
      | some (regBits, true, _, disp, rest) =>
          let dst := regR rex regBits
          if rex = canonicalRex true dst.isExtended false then some (.leaRip dst disp, rest) else none
      | some (regBits, false, baseBits, disp, rest) =>
          let dst := regR rex regBits
          let base := regB rex baseBits
          if rex = canonicalRex true dst.isExtended base.isExtended then some (.leaRM dst base disp, rest)
          else none
      | none => none := rfl

theorem decodeFromPrefix_C7 (rex : Option Rex) (tail : ByteSeq) :
    decodeFromPrefix ⟨rex, false, (0xC7 : Byte), tail⟩ =
      match readMemBaseTail tail with
      | some (digitBits, baseBits, disp, rest) =>
          if digitBits = (0 : BitVec 3) then
            match takeImm32 rest with
            | some (imm, rest2) =>
                let base := regB rex baseBits
                if rex = canonicalRex (prefW rex) false base.isExtended then
                  some (.movMI32 (if prefW rex then .w64 else .w32) base disp imm, rest2)
                else none
            | none => none
          else none
      | none => none := rfl

theorem decodeFromPrefix_FF (rex : Option Rex) (tail : ByteSeq) :
    decodeFromPrefix ⟨rex, false, (0xFF : Byte), tail⟩ =
      match decModRM tail with
      | some (digitBits, rmBits, rest) =>
          if digitBits = (0 : BitVec 3) then
            some (.inc (if prefW rex then .w64 else .w32) (regB rex rmBits), rest)
          else if digitBits = (1 : BitVec 3) then
            some (.dec (if prefW rex then .w64 else .w32) (regB rex rmBits), rest)
          else none
      | none =>
          match readMemRipTail tail with
          | some (digitBits, disp, rest) =>
              if digitBits = (2 : BitVec 3) ∧ rex = none then some (.callRip disp, rest) else none
          | none => none := rfl

private theorem movRM_correct (sz : Sz) (dst base : Gpr) (disp : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.movRM sz dst base disp) ++ rest) =
      some (Instr.movRM sz dst base disp, rest) := by
  simp only [encodeCore, bytesMem, rmBase, RmEncoding.modrm, Displacement.toBytes,
    List.nil_append, List.append_assoc]
  rw [← List.append_assoc]
  rw [decodeInstr_prefix_noescape sz.isW64 dst.isExtended (0 == (1 : BitVec 1))
    (base.rexBitV == (1 : BitVec 1))
    (by decide) (by decide), decodeFromPrefix_8B]
  simp only [List.cons_append, List.nil_append]
  have h := readMemBaseTail_bytes base disp dst.encodingBits rest
  simp only [rmBase, RmEncoding.modrm] at h
  rw [h]
  rw [rexBitV_eq_one base]
  simp only [regR_cond, regB_cond, prefW_cond]
  simp [regOfBits_self, Sz.ite_isW64, canonicalRex]

private theorem movMI32_correct (sz : Sz) (base : Gpr) (disp imm : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.movMI32 sz base disp imm) ++ rest) =
      some (Instr.movMI32 sz base disp imm, rest) := by
  simp only [encodeCore, bytesMem, rmBase, RmEncoding.modrm, Displacement.toBytes,
    List.nil_append, List.append_assoc]
  rw [← List.append_assoc]
  rw [decodeInstr_prefix_noescape sz.isW64 false (0 == (1 : BitVec 1))
    (base.rexBitV == (1 : BitVec 1))
    (by decide) (by decide), decodeFromPrefix_C7]
  simp only [List.cons_append, List.nil_append]
  have h := readMemBaseTail_bytes base disp 0 (le32 imm ++ rest)
  simp only [rmBase, RmEncoding.modrm] at h
  rw [h]
  simp only
  rw [takeImm32_le32]
  rw [rexBitV_eq_one base]
  simp only [regB_cond, prefW_cond]
  simp [regOfBits_self, Sz.ite_isW64, canonicalRex]

private theorem leaRM_correct (dst base : Gpr) (disp : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.leaRM dst base disp) ++ rest) = some (Instr.leaRM dst base disp, rest) := by
  simp only [encodeCore, bytesMem, rmBase, RmEncoding.modrm, Displacement.toBytes,
    List.nil_append, List.append_assoc]
  rw [← List.append_assoc]
  rw [decodeInstr_prefix_noescape true dst.isExtended (0 == (1 : BitVec 1))
    (base.rexBitV == (1 : BitVec 1))
    (by decide) (by decide), decodeFromPrefix_8D]
  simp only [List.cons_append, List.nil_append]
  have h := readMemFormTail_base base disp dst.encodingBits rest
  simp only [rmBase, RmEncoding.modrm] at h
  rw [h]
  rw [rexBitV_eq_one base]
  simp only [regR_cond, regB_cond]
  simp [regOfBits_self, canonicalRex]

private theorem leaRip_correct (dst : Gpr) (disp : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.leaRip dst disp) ++ rest) = some (Instr.leaRip dst disp, rest) := by
  simp only [encodeCore, bytesMem, rmRip, RmEncoding.modrm, Displacement.toBytes,
    List.nil_append, List.append_assoc]
  rw [← List.append_assoc]
  rw [decodeInstr_prefix_noescape true dst.isExtended (0 == (1 : BitVec 1)) (0 == (1 : BitVec 1))
    (by decide) (by decide), decodeFromPrefix_8D]
  simp only [List.cons_append, List.nil_append]
  have h := readMemFormTail_rip disp dst.encodingBits rest
  simp only [rmRip, RmEncoding.modrm] at h
  rw [h]
  simp only [regR_cond]
  simp [regOfBits_self, canonicalRex]

private theorem callRip_correct (disp : BitVec 32) (rest : ByteSeq) :
    decodeInstr (encodeCore (.callRip disp) ++ rest) = some (Instr.callRip disp, rest) := by
  simp only [encodeCore, bytesMem, rmRip, RmEncoding.modrm, Displacement.toBytes,
    List.nil_append, List.append_assoc]
  rw [← List.append_assoc]
  rw [decodeInstr_prefix_noescape false false (0 == (1 : BitVec 1)) (0 == (1 : BitVec 1))
    (by decide) (by decide), decodeFromPrefix_FF]
  simp only [List.cons_append, List.nil_append]
  have hNone := decModRM_rmRip_none disp 2 rest
  have hRip := readMemRipTail_bytes disp 2 rest
  simp only [rmRip, RmEncoding.modrm] at hNone hRip
  rw [hNone, hRip]
  rfl

/-- Decoding a canonical encoding recovers the instruction exactly and stops
at its end, whatever follows. One case per family: adding a new instruction
family means adding one more `_correct` lemma above and one more arm here,
never touching the others. -/
theorem decodeInstr_encodeCore (instr : Instr) (rest : ByteSeq) :
    decodeInstr (encodeCore instr ++ rest) = some (instr, rest) := by
  cases instr with
  | movRR sz dst src => exact movRR_correct sz dst src rest
  | movRI32 dst imm => exact movRI32_correct dst imm rest
  | movRI64 dst imm => exact movRI64_correct dst imm rest
  | movzxRR dstSz dst src srcIs16 => exact movzxRR_correct dstSz dst src srcIs16 rest
  | movsxRR dstSz dst src srcIs16 => exact movsxRR_correct dstSz dst src srcIs16 rest
  | aluRR op sz dst src => exact aluRR_correct op sz dst src rest
  | aluRI op sz dst imm => exact aluRI_correct op sz dst imm rest
  | testRR sz a b => exact testRR_correct sz a b rest
  | testRI sz a imm => exact testRI_correct sz a imm rest
  | shiftImm op sz dst imm => exact shiftImm_correct op sz dst imm rest
  | imul2 sz dst src => exact imul2_correct sz dst src rest
  | inc sz dst => exact inc_correct sz dst rest
  | dec sz dst => exact dec_correct sz dst rest
  | push r => exact push_correct r rest
  | pop r => exact pop_correct r rest
  | callRel32 rel => exact callRel32_correct rel rest
  | ret => exact ret_correct rest
  | jmpRel32 rel => exact jmpRel32_correct rel rest
  | jmpRel8 rel => exact jmpRel8_correct rel rest
  | jccRel32 cc rel => exact jccRel32_correct cc rel rest
  | jccRel8 cc rel => exact jccRel8_correct cc rel rest
  | syscall => exact syscall_correct rest
  | ud2 => exact ud2_correct rest
  | hlt => exact hlt_correct rest
  | nop => exact nop_correct rest
  | cdq => exact cdq_correct rest
  | cqo => exact cqo_correct rest
  | div sz src => exact div_correct sz src rest
  | idiv sz src => exact idiv_correct sz src rest
  | mul sz src => exact mul_correct sz src rest
  | setcc cc dst => exact setcc_correct cc dst rest
  | cmovcc sz cc dst src => exact cmovcc_correct sz cc dst src rest
  | xchgRR sz a b => exact xchgRR_correct sz a b rest
  | movRM sz dst base disp => exact movRM_correct sz dst base disp rest
  | movMI32 sz base disp imm => exact movMI32_correct sz base disp imm rest
  | leaRM dst base disp => exact leaRM_correct dst base disp rest
  | leaRip dst disp => exact leaRip_correct dst disp rest
  | callRip disp => exact callRip_correct disp rest

theorem decodeCore_encodeCore (instr : Instr) (rest : ByteSeq) :
    decodeCore (encodeCore instr ++ rest) = some (instr, (encodeCore instr).length) := by
  unfold decodeCore
  rw [decodeInstr_encodeCore]
  simp [List.length_append]

/-- Decoding the canonical encoding recovers the instruction exactly and
consumes exactly its bytes, whatever follows: the round-trip law
`Grass.Target.ISA.decode_encode` needs. -/
theorem decode_encode (instr : Instr) (rest : List UInt8) :
    decode (encode instr ++ rest) = some (instr, (encode instr).length) := by
  show decodeCore (((encodeCore instr).map toU8 ++ rest).map UInt8.toBitVec) = _
  rw [List.map_append, List.map_map]
  have hcomp : (UInt8.toBitVec ∘ toU8) = @id Byte := by funext b; rfl
  rw [hcomp, List.map_id, decodeCore_encodeCore]
  simp [encode]

theorem encode_pos (instr : Instr) : 0 < (encode instr).length := by
  cases instr <;>
    simp [encode, encodeCore, maybeRex, bytesMem, rmBase, rmRip, Displacement.size] <;>
    split <;> simp

end Grass.ISA.X86.Target
