import Grass.ISA.Wasm.Target.Encode
import Grass.ISA.Wasm.Target.Native
import Grass.ISA.Wasm.Target.State
import Grass.Target.ISA

/-!
# The Wasm32 ISA instance

Instantiates `Grass.Target.ISA` (`docs/TARGET_SEAMS.md`) for Wasm: `Instr`
is one Wasm instruction (`Target/Instr.lean`), `Raw` is a whole module
(`Target/Native.lean`), `State` is the whole machine — call stack, linear
memory, globals — and `step` is one instruction (`Target/State.lean`).
`encode`/`decode` and their round-trip laws live in `Target/Encode.lean`.

Nothing above this file may name a program, and nothing here names one:
`Module`/`Instr` describe the whole MVP integer family, never a particular
authored program (`docs/TARGET_SEAMS.md` rule 2).
-/
namespace Grass.ISA.Wasm

/-- The Wasm32 instance of the ISA seam. -/
def isa : Grass.Target.ISA where
  Instr := Target.Instr
  encode := Target.encode
  decode := Target.decode
  decode_encode := Target.decode_encode
  encode_pos := Target.encode_pos
  Raw := Target.Module
  InitialContext := Target.InitialContext
  State := Target.State
  initial := Target.initial
  NativeCall := Target.NativeCall
  NativeReturn := Target.NativeReturn
  Fault := Target.Fault
  step := Target.step

end Grass.ISA.Wasm
