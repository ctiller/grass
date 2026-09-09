import Grass.ISA.X86.Execution.State

namespace Grass.Tests.ISA.X86.Execution

open Grass.ISA.X86 Grass.ISA.X86.Execution

private def flags : RegisterSemantics.Flags Bool :=
  ⟨true, false, true, false, true, false⟩

-- GPR updates affect their named slot and frame the rest of the state.
example (state : State) : (state.withGpr .r10 0x1234).gpr .r10 = 0x1234 := by
  simp

example (state : State) : (state.withGpr .r10 0x1234).gpr .r11 = state.gpr .r11 := by
  apply State.withGpr_other
  decide

example (state : State) : (state.withGpr .r10 0x1234).machine = state.machine := by
  simp

-- RF (16), IF (9), and DF (10) are outside the status mask and remain visible
-- in this representation-level merge.  These are not instruction semantics.
example (state : State) (h : state.rflags = 0x10600) :
    (state.withStatusFlags flags).rflags &&& 0x10600 = 0x10600 := by
  rw [State.withStatusFlags_rflags, h]
  decide

example (state : State) : (state.withStatusFlags flags).machine = state.machine := by
  simp

example (state : State) : (state.withStatusFlags flags).gpr = state.gpr := by
  simp

example (state : State) : (state.withStatusFlags flags).statusFlags = flags := by
  exact State.withStatusFlags_statusFlags state flags

end Grass.Tests.ISA.X86.Execution
