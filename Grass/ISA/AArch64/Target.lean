import Grass.ISA.AArch64.Target.Native
import Grass.ISA.AArch64.Target.Encoding
import Grass.ISA.AArch64.Target.State
import Grass.ISA.AArch64.Target.Step
import Grass.Target.ISA

/-!
# The AArch64 instance of `Grass.Target.ISA`

`Grass.ISA.AArch64.isa` fills `Grass.Target.ISA` (`docs/TARGET_SEAMS.md`):
`Instr`/`encode`/`decode`/`decode_encode`/`encode_pos` from
`Grass.ISA.AArch64.Target.Encoding`, `Raw` is the shared
`Grass.Target.Sectioned` (`Grass/Target/Raw.lean`), `InitialContext`/
`NativeCall`/`NativeReturn`/`Fault` from `Grass.ISA.AArch64.Target.Native`,
`State`/`initial` from `Grass.ISA.AArch64.Target.State`, and `step` from
`Grass.ISA.AArch64.Target.Step`.

## Coverage

Resolved-instruction families with a proved round-trip and wired-up
semantics: move-wide (`movz`/`movn`/`movk`), add/subtract immediate
(`add`/`adds`/`sub`/`subs`/`cmp`/`cmn` as `setFlags` + destination-register
choices — no separate alias constructors), add/subtract shifted-register
(same six mnemonics, register form, `lsl`/`lsr`/`asr` shift), logical
immediate (`and`/`orr`/`eor`, restricted to a 64-bit contiguous low-order
bitmask — see `Grass.ISA.AArch64.Target.Encoding.LogicalImm`), load/store
unsigned-offset (`ldr`/`str`/`ldrb`/`strb`, 64/32-bit and byte), `cbz`
(reusing `Grass.ISA.AArch64.Control.CompareZero`, already cited and proved
there), `svc` (reusing `Control.SupervisorCall`, stepping to `.external`
carrying `CallTarget.supervisor`), and `hlt` (stepping to `.halted`).

Not covered — encoded nowhere in `Target.Encoding`, so absent from `Instr`,
`step`, and every proof, rather than present with an unverified encoding or
an unproved dispatch case (`docs/TARGET_SEAMS.md` rule 5, and the brief's
"leave a family out rather than leave a gap"): `mov` (register), `and`/`orr`/
`eor` shifted-register, `lsl`/`lsr`/`asr` immediate, `b`, `bl`, `b.cond`,
`cbnz`, `tbz`/`tbnz`, `adr`/`adrp`, `ldp`/`stp` (any addressing mode),
register-offset and pre/post-index load/store, `br`/`blr`/`ret`, `brk`,
`nop`, `mul`, `udiv`/`sdiv`, `csel`/`cset`. `Grass/ISA/AArch64/Target/
Encoding.lean`'s module docstring records why: this pass established, for
each covered family, an inequality against every earlier family's fixed bits
provable without `bv_decide`'s SAT backend (the axiom
`docs/DECISIONS.md` 31 rejects); the families above were left for a
follow-up that budgets the same care per family rather than shipped with a
guessed bit layout or a dispatch gap.
-/

namespace Grass.ISA.AArch64

open Grass.ISA.AArch64.Target

theorem Target.encode_length (instr : Target.Instr) : (Target.encode instr).length = 4 := by
  cases instr <;> simp [Target.encode, Target.Instr.toWord, Target.wordToBytes]

theorem Target.decode_encode' (instr : Target.Instr) (rest : List UInt8) :
    Target.decode (Target.encode instr ++ rest) = some (instr, (Target.encode instr).length) := by
  rw [Target.encode_length, Target.decode_encode instr rest]

/-- The AArch64 instance of the ISA seam. -/
def isa : Grass.Target.ISA where
  Instr := Target.Instr
  encode := Target.encode
  decode := Target.decode
  decode_encode := Target.decode_encode'
  encode_pos := Target.encode_pos
  Raw := Grass.Target.Sectioned
  InitialContext := InitialContext
  State := Target.State
  initial := Target.initial
  NativeCall := NativeCall
  NativeReturn := NativeReturn
  Fault := Fault
  step := Target.step

end Grass.ISA.AArch64
