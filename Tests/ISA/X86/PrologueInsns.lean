import Grass.ISA.X86.Bytes
import Grass.ISA.X86.Decode

/-!
# Byte-level fixtures for the two Win64 prologue instruction forms

`Grass.ISA.X86.pushR64` and `Grass.ISA.X86.subR64Imm8`/`subR64Imm32` exist to
close the encoder half of the obligation in `Grass/ABI/Win64/UnwindBytes.lean`:
`Layout.WellFormed` constrains code offsets against each other but never against
bytes an assembler would emit. An encoder nobody checks would move that
obligation rather than close it, so the encodings are pinned here.

Two independent oracles, because neither alone is enough.

**Pinned bytes.** The literals below are the encodings the vendor tables
specify: `50+rd` for `PUSH r64`, `REX.W + 83 /5 ib` and `REX.W + 81 /5 id` for
the two `SUB` forms. These are ground truth from the manuals, not from this
library, so they falsify an encoder that is self-consistently wrong -- a swapped
`REX.B`, a `/4` instead of `/5`, a missing `REX.W`.

**Decoder round-trip.** `decodeInsn` is a separate code path built from the
opcode table, and it is what says the *lengths* are right: it must find a row
for `0x50+rd`, `0x81` and `0x83`, and must agree on how many immediate bytes
follow. A length disagreement is the failure that matters here, because unwind
code offsets count bytes, so an encoder one byte off makes every later offset in
a prologue wrong. The round-trip also consumes the whole byte string and leaves
no remainder, which is the check that the instruction does not run short.

The two oracles do share `InsnEncoding` and `decodeOperands`, as
`Tests/ISA/X86/DecodeCorpus.lean` notes of itself. That is why the pinned bytes
are here as well: they depend on neither.
-/

namespace Tests.ISA.X86.PrologueInsns

open Grass.ISA.X86

/-! ## `PUSH r64` -/

/-- `push rbx` is a single byte: no `REX`, and `rbx` rides in the opcode. -/
example : (pushR64 .rbx).toBytes = [0x53] := rfl

/-- `push rbp`. -/
example : (pushR64 .rbp).toBytes = [0x55] := rfl

/-- `push rsi`. -/
example : (pushR64 .rsi).toBytes = [0x56] := rfl

/-- `push rdi`. -/
example : (pushR64 .rdi).toBytes = [0x57] := rfl

/-- `push r12` needs `REX.B`, so it is two bytes and the opcode's low three bits
are `r12`'s, which are `rsp`'s too. The prefix is `41`, carrying `B` and not
`R`: the register is in the opcode, not in a `ModR/M` `reg` field. -/
example : (pushR64 .r12).toBytes = [0x41, 0x54] := rfl

/-- `push r15`. -/
example : (pushR64 .r15).toBytes = [0x41, 0x57] := rfl

/-- The length difference the unwind layer depends on: saving a legacy register
costs one byte and saving an extended one costs two, so a prologue's second
code offset is 1 or 2 depending on which register came first. -/
example : (pushR64 .rbx).size = 1 := rfl
example : (pushR64 .r12).size = 2 := rfl

/-! ## `SUB r64, imm` -/

/-- `sub rsp, 32` -- the classic shadow-space-plus-locals allocation.
`EC` is `mod=11, reg=101, rm=100`: register-direct, `/5`, `rsp`. -/
example : (subR64Imm8 .rsp 32).toBytes = [0x48, 0x83, 0xEC, 0x20] := rfl

/-- `sub rsp, 8`. -/
example : (subR64Imm8 .rsp 8).toBytes = [0x48, 0x83, 0xEC, 0x08] := rfl

/-- `sub rsp, 4096`, the `imm32` form: `81` rather than `83`, and four
little-endian immediate bytes. -/
example : (subR64Imm32 .rsp 4096).toBytes =
    [0x48, 0x81, 0xEC, 0x00, 0x10, 0x00, 0x00] := rfl

/-- The other length fact: a small allocation is four bytes and a large one is
seven. `UNWIND_CODE` offsets after a `sub rsp` differ by three depending on
which form the assembler chose. -/
example : (subR64Imm8 .rsp 32).size = 4 := rfl
example : (subR64Imm32 .rsp 4096).size = 7 := rfl

/-- `REX.B` reaches an extended register here too, and lands in the same prefix
byte as `REX.W`: `sub r12, 16` is `49`, not `48`. -/
example : (subR64Imm8 .r12 16).toBytes = [0x49, 0x83, 0xEC, 0x10] := rfl

/-! ## Decoder round-trip

Each encoding decodes back to itself with nothing left over. -/

example : decodeInsn (pushR64 .rbx).toBytes = .ok (pushR64 .rbx, []) := rfl
example : decodeInsn (pushR64 .r12).toBytes = .ok (pushR64 .r12, []) := rfl
example : decodeInsn (pushR64 .r15).toBytes = .ok (pushR64 .r15, []) := rfl
example : decodeInsn (subR64Imm8 .rsp 32).toBytes =
    .ok (subR64Imm8 .rsp 32, []) := rfl
example : decodeInsn (subR64Imm32 .rsp 4096).toBytes =
    .ok (subR64Imm32 .rsp 4096, []) := rfl
example : decodeInsn (subR64Imm8 .r12 16).toBytes =
    .ok (subR64Imm8 .r12 16, []) := rfl

/-- A `push` followed by a `sub` decodes as two instructions, the second
starting exactly where the first ended. This is the property a wrong length
destroys, and it is the one the unwind offsets rest on. -/
example :
    decodeInsn ((pushR64 .rbx).toBytes ++ (subR64Imm8 .rsp 32).toBytes) =
      .ok (pushR64 .rbx, (subR64Imm8 .rsp 32).toBytes) := rfl

/-! ## The residue `InsnEncoding.WellFormed` leaves

That header records what `WellFormed` does not check: the immediate is
unconstrained there, because the module has no opcode table. The instruction
layer discharges it for everything this library emits -- `MatchesSpec` reads the
immediate width off the table, and all nine encoders have a round-trip corollary
taking it as a premise.

What survives is the gap between what the library emits and what its types
permit. This is that gap, as a witness rather than a sentence. -/

/-- A `lea` carrying a four-byte immediate. `0x8D` takes none, so the decoder
would read the four bytes as the start of the next instruction and resume inside
it -- the length failure `Tests/ISA/X86/DecodeCorpus.lean` exists to catch. -/
def leaWithStrayImmediate : InsnEncoding :=
  { rex := some (Rex.of true false false false)
    escape := false
    opcode := 0x8D
    modrm := some ⟨ModRm.modRegisterDirect, 0, 0⟩
    sib := Option.none
    disp := .none
    imm := .i32 0x11223344 }

/-- `WellFormed` accepts it. Nothing here is about the opcode. -/
example : leaWithStrayImmediate.WellFormed := by decide

/-- `MatchesSpec` against the row `findSpec` returns for `0x8D` refuses it, so
the constraint exists -- one layer up, where the table is. -/
example : ¬ (∃ s, findSpec false 0x8D = some s ∧
    MatchesSpec leaWithStrayImmediate s) := by decide

/-- The refusal above is not vacuous: the table does have a row for `0x8D`, so
`MatchesSpec` is being evaluated against a real one rather than failing for want
of anything to compare with. -/
example : (findSpec false 0x8D).isSome := by decide

/-- And the immediate is the field doing it. The same record with no immediate
matches the row, so the three fields `MatchesSpec` shares with `WellFormed`'s
concerns -- escape, opcode, ModR/M presence -- are all already in agreement, and
only the immediate width differs. Without this the refusal above would not say
which field was wrong. -/
example : ∃ s, findSpec false 0x8D = some s ∧
    MatchesSpec { leaWithStrayImmediate with imm := .none } s := by decide

/-- And the encoders cannot build it: `leaR64` fixes the immediate to `.none`,
so no argument reaches this record. That is why the residue is about
hand-written values and not about anything the library emits. -/
example (dst : Gpr) (m : MemOperand) (i : InsnEncoding) :
    leaR64 dst m = some i → i.imm = .none := by
  intro h
  simp only [leaR64, encodeMemInsn, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

end Tests.ISA.X86.PrologueInsns
