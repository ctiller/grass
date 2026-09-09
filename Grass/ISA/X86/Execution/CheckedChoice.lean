import Grass.ISA.X86.Execution.State

/-!
# Explicit choices at the checked CPU boundary

`CheckedChoice.normal` supplies six status bits, not a replacement CPU state.
The instruction relation must admit them using the production partial-flags
constraints. Non-arithmetic instructions need not use that choice.

The other alternatives name requested event classes only. Their presence gives
no event timing, fault priority, delivery, admission or physical coverage law.
An uncovered alternative remains an explicit modeling obligation.
-/

namespace Grass.ISA.X86.Execution

inductive CheckedChoice where
  | normal (status : RegisterSemantics.Flags Bool)
  | fault (class_ : Grass.Memory.FaultClassId)
  | trap (class_ : Grass.Memory.FaultClassId)
  | interruption (vector : BitVec 8)
  | abort (class_ : Grass.Memory.FaultClassId)
deriving DecidableEq, Repr

end Grass.ISA.X86.Execution
