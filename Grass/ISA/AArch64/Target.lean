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

Fifteen resolved-instruction families, each with a proved round-trip,
pairwise dispatch disjointness against every other family, and wired-up
semantics:

- move-wide (`movz`/`movn`/`movk`);
- add/subtract immediate and shifted-register (`add`/`adds`/`sub`/`subs`/
  `cmp`/`cmn` as `setFlags` + destination-register choices — no separate
  alias constructors; `lsl`/`lsr`/`asr` shift on the register form);
- logical immediate (`and`/`orr`/`eor`, restricted to a 64-bit contiguous
  low-order bitmask — see `Target.Encoding.LogicalImm`) and logical
  shifted-register (`and`/`orr`/`eor`/`ands`, restricted to `N = 0`; `mov`
  and `tst` fall out of the zero-register/discard-on-write convention rather
  than a separate alias constructor);
- load/store unsigned-offset (`ldr`/`str`/`ldrb`/`strb`, 64/32-bit and byte);
- `cbz`/`svc` (reusing `Grass.ISA.AArch64.Control.CompareZero`/
  `SupervisorCall`, already cited and proved there) and the dedicated
  `cbnz` (the same shape, `Control.lean` being out of scope for this pass);
- `hlt` (steps to `.halted`) and `nop` (`hint #0`, steps forward);
- `b`/`bl` (imm26, `bl` writes `pc + 4` to `x30`), `br`/`blr`/`ret`
  (register-indirect, ordinary control transfer — no import slot modeled),
  and `b.cond` (imm19 + the full 16-way NZCV condition table);
- `adr`/`adrp` (PC-relative address; `adrp` masks the low 12 bits of `pc`).

`svc` steps to `.external` carrying `CallTarget.supervisor`; every other
family is `.internal` except `hlt` (`.halted`).

Not covered — encoded nowhere in `Target.Encoding`, so absent from `Instr`,
`step`, and every proof, rather than present with an unverified encoding or
an unproved dispatch case (`docs/TARGET_SEAMS.md` rule 5, and the brief's
"leave a family out rather than leave a gap"): `tbz`/`tbnz`, `ldp`/`stp` (any
addressing mode), register-offset and pre/post-index load/store immediate9,
`brk`, `madd`/`mul`, `udiv`/`sdiv`, `csel`/`csinc`/`cset`, `ubfm`/`sbfm`
(`lsl`/`lsr`/`asr` immediate). `Grass/ISA/AArch64/Target/Encoding.lean`'s
module docstring records why: this pass established, for each covered
family, an inequality against every earlier family's fixed bits provable
without `bv_decide`'s SAT backend (the axiom `docs/DECISIONS.md` 31
rejects); the families above were left for a follow-up that budgets the same
care per family rather than shipped with a guessed bit layout or a dispatch
gap.
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
