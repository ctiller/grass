import Grass.Disasm.StoreAttempt
import Grass.Memory.SpatialAccess

/-! Compose decoded footprint evidence with the existing memory bounds checker.
This produces a conditional spatial assessment, not a concrete execution witness:
the consumer still owes fetched bytes, entry applicability and a history-consistent
caller pointer/object contract. Neither a successful write nor a checker denial
is required to expose the candidate footprint. -/
namespace Grass.Disasm.Spatial

open Grass.Memory Grass.Memory.SpatialAccess Grass.ISA.X86.Execution

/-- Preserve the decoder's exact address and width rather than accepting a second
unrelated footprint from the caller. -/
def footprint {rip bytes state} (decoded : StoreAttempt.Evidence rip bytes state) : WriteFootprint :=
  ⟨decoded.address, decoded.width, decoded.footprint_noWrap⟩

/-- Both alternatives concern the same object in the decoded register state's
memory and exactly the same candidate write range. -/
inductive Assessment {rip bytes state provenance}
    (decoded : StoreAttempt.Evidence rip bytes state)
    (object : PlacedObject state.machine.memory provenance) where
  | within (proof : WithinObject object (footprint decoded))
  | outside (index : Nat) (proof : OutsideByte object (footprint decoded) index)

/-- Run the shared memory checker on the exact decoded footprint. The resulting
proof is conditional on the caller's object association, not evidence recovering
that association from numerical address equality. -/
def assess {rip bytes state provenance} (decoded : StoreAttempt.Evidence rip bytes state)
    (object : PlacedObject state.machine.memory provenance) : Assessment decoded object :=
  match checked : outsideIndex? object (footprint decoded) with
  | none => .within ((outsideIndex?_eq_none_iff object (footprint decoded)).mp checked)
  | some index => .outside index (outsideIndex?_sound object (footprint decoded) checked)

/-- An excluded decoded byte refutes the exact same spatial-coverage claim. -/
theorem excluded_not_within {rip bytes state provenance}
    (decoded : StoreAttempt.Evidence rip bytes state)
    (object : PlacedObject state.machine.memory provenance) {index : Nat}
    (outside : OutsideByte object (footprint decoded) index) :
    ¬ WithinObject object (footprint decoded) := outside.not_within

end Grass.Disasm.Spatial
