import Grass.Disasm.CallerObject

namespace Grass.Tests.Disasm.CallerObject

open Grass.Disasm.CallerObject Grass.Memory Grass.Std.Logical

private def checkError (base : MachineAddress) (objectSize rootSize : Nat)
    (rip : MachineAddress) : Option Error :=
  match check base objectSize rootSize rip with
  | .error error => some error
  | .ok _ => none

example : (check 0x1000 8 16 0x140001000).map
    (fun result => (result.state.gpr .rcx, result.state.rip,
      result.provenance.extent, result.provenance.rootExtent,
      result.object.base)) =
    .ok (0x1000, 0x140001000, ⟨0, 8⟩, ⟨0, 16⟩, 0x1000) := by rfl

example : checkError 0x1000 17 16 0x140001000 = some .objectOutsideRoot := by rfl

example : checkError (0 - 8) 8 16 0x140001000 = some .placementWraps := by rfl

end Grass.Tests.Disasm.CallerObject
