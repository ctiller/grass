import Grass.ISA.X86.Execution.State
import Grass.ISA.X86.Execution.DecodedSite
import Grass.Op.Step

/-!
# CPU outcome vocabulary

This module defines representation, not an execution relation or a coverage
theorem. A future fixed CPU step relation must derive each outcome from actual
fetch, instruction and event-delivery evidence. Constructing an outcome value
does not certify that it can occur on a processor.

The canonical architectural carrier is `State`. Windows protocol metadata,
invocation identities, provider servicing and ABI summary returns belong to the
platform composition. In particular, `CpuEvent.returned` denotes a literal CPU
return instruction, not a protocol-table update.
-/

namespace Grass.ISA.X86.Execution

/-- The CPU boundary reached by a checked transition.

Fault, trap, interruption and abort events describe a state before platform
delivery. Their constructors provide no rollback, saved-RFLAGS or handler-entry
law; the instruction/profile relation must supply those facts. -/
inductive CpuEvent where
  | completed
  /-- The target is the resulting state's RIP; this value is the saved continuation. -/
  | called (continuation : BitVec 64)
  /-- Literal CPU RET; the target is the resulting state's RIP. -/
  | returned
  | fault (class_ : Grass.Memory.FaultClassId)
  | trap (class_ : Grass.Memory.FaultClassId)
  | interruption (vector : BitVec 8)
  | abort (class_ : Grass.Memory.FaultClassId)
deriving DecidableEq, Repr

/-- A reason the bounded CPU model has not covered an execution.

These are applicability diagnostics, not architectural fault classifications.
In particular, a canonical decoder error can denote a form outside this model,
and does not establish an architectural invalid-opcode exception. -/
inductive ApplicabilityFailure where
  | decode (error : DecodedSite.Error)
  | trailingBytes
  | instruction (encoding : InsnEncoding)
  | operation (reason : Grass.Op.StepRejection)
  | faultTransfer (class_ : Grass.Memory.FaultClassId)
  | trapTransfer (class_ : Grass.Memory.FaultClassId)
  | interruptionTransfer (vector : BitVec 8)
  | abortTransfer (class_ : Grass.Memory.FaultClassId)
deriving DecidableEq, Repr

/-- A CPU outcome or an explicitly uncovered prefix.

`outsideProfile` retains the actual reached prefix state when supplied by a step
receipt. `outsideProfile` is not successful termination, a physical no-op or a proof that
execution cannot continue. A program certificate must cover that alternative or
prove it unreachable under its admitted inputs. -/
inductive CpuOutcome where
  | progressed (after : State) (event : CpuEvent)
  | outsideProfile (reached : State) (reason : ApplicabilityFailure)

/-- The single architectural state carried by either outcome variant. -/
def CpuOutcome.state : CpuOutcome → State
  | .progressed after _ => after
  | .outsideProfile reached _ => reached

@[simp] theorem CpuOutcome.state_progressed (after : State) (event : CpuEvent) :
    (CpuOutcome.progressed after event).state = after := rfl

@[simp] theorem CpuOutcome.state_outsideProfile (reached : State) (reason : ApplicabilityFailure) :
    (CpuOutcome.outsideProfile reached reason).state = reached := rfl

end Grass.ISA.X86.Execution
