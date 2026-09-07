import Grass.ISA.X86.Addressing

/-!
# Spike 1 addressing encodings

Golden byte values for the exact addressing forms in
`Spikes/1_Hello_World/Program.lean`, checked by decision at build time.

`Tests/Memory/Spike1Reference.lean` declares the *memory effects* of the same
instruction mix, and says of them: "The point is not that these are correct
x86-64 models — the ISA agent owns that, and these deliberately do not claim a
citation." This file is the other half. It says nothing about memory effects and
everything about which bytes come out.

## Why literal expected bytes

`Grass/ISA/X86/Encoding.lean` proves encoder and decoder inverse, and
`Grass/ISA/X86/Addressing.lean` proves every encodable operand decodes back to
itself. Neither would notice if the whole model had the ModR/M field order
reversed: a self-consistent encoder that agrees with its own decoder round-trips
perfectly and emits bytes no processor will execute.

Round-trip theorems establish internal consistency. Only comparison against an
externally known byte establishes that the model is about x86-64. So the
expected values here are written as literals — the encodings a Win64 program
uses for these exact forms — and the model is checked against them, never the
other way around.

These are *fixtures*, not authority. `docs/VALIDATION.md` §2 puts the real check
in the differential and physical-probe layers, against independent assemblers and
real hardware. These catch a transposed field in the second it takes to
elaborate the file.

## The four forms

Spike 1 uses exactly these, and no others:

| source | form | bytes |
| --- | --- | --- |
| `call qword ptr [rip + __imp_GetStdHandle]` | RIP-relative, `FF /2` | `FF 15 d32` |
| `lea r13, [rip + payload]` | RIP-relative, extended reg | `4C 8D 2D d32` |
| `mov transferred, 0` | `[rsp + d]`, `C7 /0` | `C7 84 24 d32 imm32` |
| `lea r9, transferred.addr` | `[rsp + d]` | `4C 8D 8C 24 d32` |

The `rsp` rows are the ones worth staring at. The `24` is a SIB byte that exists
only because `rsp`'s register number is the SIB escape; an encoder that emitted
`rm=100` without it would produce a shorter, entirely plausible, wrong
instruction that addresses something else.

## Why the displacement is concrete

The ModR/M, SIB and REX bytes do not depend on the displacement's value — they
are determined by the operand's shape. A fixed displacement is used anyway so
every fact here is closed and settled by `decide` rather than by rewriting, and
so the round-trip cases at the end carry a value that would be visibly wrong if
it were dropped or truncated. `0x11223344` is chosen to have four distinct
non-zero bytes for exactly that reason.
-/

namespace Grass.Tests.ISA.X86.Spike1

open Grass.Std.Logical Grass.ISA.X86

/-- A displacement with four distinct non-zero bytes, so that a truncation or a
byte-order mistake is visible rather than accidentally correct. -/
def disp : BitVec 32 := 0x11223344

/-- `[rip + disp]`, used by both import calls and by `lea r13, [rip + payload]`. -/
def ripForm : Option RmEncoding := encodeMem (.ripRelative disp)

/-- `[rsp + disp]`, the stack slot holding `transferred`. -/
def rspForm : Option RmEncoding := encodeMem (.base .rsp disp)

/-! ## `call qword ptr [rip + disp32]`

`FF /2`: the ModR/M `reg` field is the opcode extension `2`, not a register.
-/

/-- The ModR/M byte of a RIP-relative indirect call is `0x15`. -/
theorem call_rip_modrm : ripForm.map (fun e => (e.modrm 2).toByte) = some 0x15 := by
  decide

/-- No SIB byte follows. -/
theorem call_rip_no_sib : ripForm.map (·.sib) = some Option.none := by decide

/-- It needs no REX prefix: the address supplies no extension bits. -/
theorem call_rip_needs_no_rex : ripForm.map (·.needsRex) = some false := by decide

/-! ## `lea r13, [rip + payload]`

`REX.W + 8D /r`, with `r13` in the `reg` field.
-/

/-- The prefix is `0x4C`: `REX.W` for the 64-bit destination, `REX.R` for
`r13`. -/
theorem lea_r13_rip_rex :
    ripForm.map (fun e => (e.rex true (Gpr.rexBit .r13)).toByte) = some 0x4C := by
  decide

/-- The ModR/M byte is `0x2D`: `mod=00`, `reg=101` (r13's low bits), `rm=101`
(the RIP-relative escape).

Both fields are `101` here for unrelated reasons, which is the kind of
coincidence a transposed-field bug hides behind — so the `rsp` cases below,
where the fields differ, carry the weight. -/
theorem lea_r13_rip_modrm :
    ripForm.map (fun e => (e.modrm (Gpr.encodingBits .r13)).toByte) = some 0x2D := by
  decide

/-! ## `mov dword ptr [rsp + disp32], 0`

`C7 /0`: the `reg` field is the opcode extension `0`.
-/

/-- The ModR/M byte is `0x84`: `mod=10`, `reg=000`, `rm=100`. The `rm=100` is
the SIB escape, not a register. -/
theorem mov_rsp_modrm : rspForm.map (fun e => (e.modrm 0).toByte) = some 0x84 := by
  decide

/-- The SIB byte is `0x24`: scale 1, no index, base `rsp`.

This byte is the whole point of the form. Without it the instruction would be
one byte shorter and would address something else entirely. -/
theorem mov_rsp_sib :
    rspForm.map (fun e => e.sib.map (·.toByte)) = some (some 0x24) := by decide

/-- It needs no REX prefix: `rsp` is not an extended register. -/
theorem mov_rsp_needs_no_rex : rspForm.map (·.needsRex) = some false := by decide

/-! ## `lea r9, [rsp + disp32]` -/

/-- The prefix is `0x4C`: `REX.W` and `REX.R` for `r9`. -/
theorem lea_r9_rsp_rex :
    rspForm.map (fun e => (e.rex true (Gpr.rexBit .r9)).toByte) = some 0x4C := by
  decide

/-- The ModR/M byte is `0x8C`: `mod=10`, `reg=001` (r9's low bits), `rm=100`. -/
theorem lea_r9_rsp_modrm :
    rspForm.map (fun e => (e.modrm (Gpr.encodingBits .r9)).toByte) = some 0x8C := by
  decide

/-- The same `0x24` SIB byte. The base is a property of the address, not of the
register being loaded, and this checks that the two do not interfere. -/
theorem lea_r9_rsp_sib :
    rspForm.map (fun e => e.sib.map (·.toByte)) = some (some 0x24) := by decide

/-! ## Negative fixtures

The bytes that must *not* come out. Each is an encoding a plausible
implementation produces and a processor misreads.
-/

/-- A RIP-relative operand is never encoded as an absolute address.

The absolute form's ModR/M byte for `FF /2` is `0x14` — `mod=00, reg=010,
rm=100`, an address through a SIB byte with no base. The RIP-relative form is
`0x15`. A 32-bit-mode encoder confuses these, and this pins the difference. -/
theorem call_rip_is_not_absolute :
    ripForm.map (fun e => (e.modrm 2).toByte) ≠
      (encodeMem (.absolute disp)).map (fun e => (e.modrm 2).toByte) := by decide

/-- An `rsp` base always carries a SIB byte. -/
theorem rsp_form_always_has_sib :
    rspForm.map (fun e => e.sib.isSome) = some true := by decide

/-- So does `r12`, for a reason that has nothing to do with `r12`: it shares
`rsp`'s low three bits. Spike 1 keeps the standard-output handle in `r12` across
the write loop. -/
theorem r12_form_always_has_sib :
    (encodeMem (.base .r12 disp)).map (fun e => e.sib.isSome) = some true := by decide

/-- `r13` never gets `mod=00`.

Spike 1 uses `r13` as the payload cursor. `mod=00` with `r13`'s low bits is the
RIP-relative escape, so `[r13]` encoded that way would silently become
`[rip + 0]` — a valid instruction reading the wrong memory. -/
theorem r13_base_never_mod00 :
    (encodeMem (.base .r13 disp)).map (·.mod) ≠ some ModRm.modNoDisplacement := by
  decide

/-- `rsp` has no encoding as an index register, so no form of Spike 1's
addressing can accidentally acquire one. -/
theorem no_rsp_index :
    encodeMem (.baseIndex .r13 .rsp .s1 disp) = Option.none := by decide

/-! ## Round-trip on the exact Spike 1 forms

The general theorem is `Grass.ISA.X86.encode_then_decode`. These instances also
check that the displacement survives, which the shape-only facts above do not.
-/

/-- `[rip + disp]` decodes back to itself, displacement intact. -/
theorem rip_round_trip : ripForm.bind decodeMem = some (.ripRelative disp) := by
  decide

/-- `[rsp + disp]` decodes back to itself, and to `rsp` rather than to the
absent register the SIB escape could have been read as. -/
theorem rsp_round_trip : rspForm.bind decodeMem = some (.base .rsp disp) := by
  decide

/-- `[r12 + disp]` decodes back to `r12`, not to `rsp`, even though they share
the ModR/M and SIB fields and differ only in `REX.B`. -/
theorem r12_round_trip :
    (encodeMem (.base .r12 disp)).bind decodeMem = some (.base .r12 disp) := by
  decide

/-- `[r13 + disp]` decodes back to `r13`, not to a RIP-relative address. -/
theorem r13_round_trip :
    (encodeMem (.base .r13 disp)).bind decodeMem = some (.base .r13 disp) := by
  decide

end Grass.Tests.ISA.X86.Spike1
