import Grass.ISA.X86.Execution.ObservedFetch
import Grass.ISA.X86.Execution.Instruction
import Grass.ISA.X86.Execution.RawOutcome

/-!
# Fixed classification of an actual instruction-byte observation

`dispatch` performs canonical decoding, whole-instruction admission and fixed
semantic-family selection. It does not execute the selected instruction or
choose an operation, descriptor or fault plan. Consequently it is not the total
CPU step relation. A failed classification retains the already observed prefix
state through `failureOutcome`; it is not an architectural invalid-opcode proof.
-/

namespace Grass.ISA.X86.Execution

/-- An actual decoded fetch with its fixed semantic-family selection. -/
structure Dispatched (before : State) (after : Grass.Memory.MachineState) where
  fetch : FetchedSite before after
  selection : Instruction.Selection fetch.site.encoding
  selected : Instruction.select fetch.site.encoding = some selection

namespace ObservedFetch

/-- The architectural register view paired with the actual execute-read result. -/
def reachedState {before : State} {after : Grass.Memory.MachineState}
    (_fetch : ObservedFetch before after) : State := { before with machine := after }

private def decoded {before : State} {after : Grass.Memory.MachineState}
    (fetch : ObservedFetch before after) : Except ApplicabilityFailure (FetchedSite before after) :=
  match DecodedSite.check before.rip fetch.bytes with
  | .error error => .error (.decode error)
  | .ok site =>
      if noTrailing : site.rest = [] then
        .ok
          { descriptor := fetch.descriptor
            run := fetch.run
            writeData := fetch.writeData
            indeterminate := fetch.indeterminate
            memoryOracle := fetch.memoryOracle
            intent := fetch.intent
            initialization := fetch.initialization
            ledgerEffect := fetch.ledgerEffect
            authorityEffect := fetch.authorityEffect
            address := fetch.address
            placed := fetch.placed
            site := site
            noTrailing := noTrailing }
      else .error .trailingBytes

/-- `dispatch` selects a family from the whole actual observation using the fixed classifier. -/
def dispatch {before : State} {after : Grass.Memory.MachineState}
    (fetch : ObservedFetch before after) : Except ApplicabilityFailure (Dispatched before after) :=
  match fetch.decoded with
  | .error reason => .error reason
  | .ok site =>
      match selected : Instruction.select site.site.encoding with
      | none => .error (.instruction site.site.encoding)
      | some selection => .ok ⟨site, selection, selected⟩

/-- `failureOutcome` represents a demonstrated classification failure with the actual reached state. -/
def failureOutcome {before : State} {after : Grass.Memory.MachineState}
    (fetch : ObservedFetch before after) (reason : ApplicabilityFailure)
    (_failed : fetch.dispatch = .error reason) : CpuOutcome :=
  .outsideProfile fetch.reachedState reason

/-- `failureOutcome_machine` retains the actual execute-read machine on a failed dispatch. -/
theorem failureOutcome_machine {before : State} {after : Grass.Memory.MachineState}
    (fetch : ObservedFetch before after) (reason : ApplicabilityFailure)
    (failed : fetch.dispatch = .error reason) :
    (fetch.failureOutcome reason failed).state.machine = after := rfl

end ObservedFetch
end Grass.ISA.X86.Execution
