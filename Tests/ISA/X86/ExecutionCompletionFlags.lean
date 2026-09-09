import Grass.ISA.X86.Execution.CompletionFlags

namespace Grass.Tests.ISA.X86.ExecutionCompletionFlags
open Grass.ISA.X86 Grass.ISA.X86.Execution

-- An RF=1 input must not pass through a completed PUSH unchanged.
example (state : State) (h : state.rflags = 0x10602) :
    completedPushRflags state = 0x602 := by rw [completedPushRflags, h]; decide

-- No IF=0 or DF=0 entry assumption: completed SUB changes neither, but clears RF.
example (state : State) (hf : state.rflags = 0x10602) (hr : state.gpr .rsp = 0x1000) :
    completedSubRflags state (.i8 48) = 0x602 := by
  simp [completedSubRflags, State.withStatusFlags, completedSubStatus, hf, hr,
    State.statusFlags, RegisterSemantics.evaluateImmediate, RegisterSemantics.evaluate,
    RegisterSemantics.Flags.map, RegisterSemantics.Flags.bits, resumeMask, statusMask]
  decide

end Grass.Tests.ISA.X86.ExecutionCompletionFlags
