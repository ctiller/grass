import Tests.Platform.Win32LoaderEntry
import Grass.Platform.Win32.GetStdHandleStackPlan
import Grass.ISA.X86.Execution.ComputationFactory
import Grass.ISA.X86.Execution.CallFactory
import Grass.ISA.X86.Execution.MemoryMoveFactory

/-!
# Actual source-linked Hello prefix through GetStdHandle CALL

This fixture executes the unchanged checked-in source through loading, its
derived prologue, the source-authored `mov ecx, STD_OUTPUT_HANDLE`, and the
first indirect CALL. The return-frame slots are then derived from that actual
CALL result. It stops before provider entry: no registration, custody, provider
result, or native execution correspondence is fabricated here.
-/

namespace Grass.Tests.Win32HelloCall

open Grass.Artifact Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Execute exactly the generated initializer sequence, recomputing the fixed
Windows policy at every reached state and checking each fetched encoding
against its source-derived initializer entry. -/
def runInitializations {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    List Grass.Assembly.SourceInitialization.Entry → State → Option State
  | [], before => some before
  | expected :: rest, before =>
      match Cpu.policy? loaded before with
      | none => none
      | some policy =>
          match MemoryMoveFactory.memoryMove policy before with
          | .error _ => none
          | .ok initialized =>
              if initialized.fetched.dispatched.fetch.site.encoding = expected.store.encoding then
                runInitializations loaded rest initialized.execution.result
              else none

/-- The complete checked prefix and deterministic frame-plan checks. Expected
values are obtained from the retained receipts and ABI definitions rather than
handwritten instruction bytes or stack offsets. -/
def actualPrefix? : Option Bool := do
  let body ← (Grass.Assembly.SourceInput.extractHelloSourceChars
    Grass.Tests.Assembly.SourceResolve.authored).toOption
  let frame ← Grass.Assembly.SourceFrame.derive? body
  let splice ← Grass.Assembly.SourceSplice.derive? frame 0
  let plan ← Grass.Tests.Win32LoaderEntry.helloPlan?
  let image : ImageInput := ⟨plan, (PE.writeImage plan).toHostBytes, rfl⟩
  let inputs := Grass.Tests.Win32LoaderEntry.inputsFor plan
    (.fromList [.fromList [0x7ff01000, 0x7ff02000, 0x7ff03000]])
  let loaded ← initialize? image inputs
  match Grass.Assembly.PrologueFactory.execute loaded splice.prologue loaded.initialState with
  | .error _ => none
  | .ok ⟨afterPrologue, _⟩ =>
      match runInitializations loaded splice.initialization.entries afterPrologue with
      | none => none
      | some afterInitialization =>
              match _movePolicyExact : Cpu.policy? loaded afterInitialization with
              | none => none
              | some movePolicy =>
                  match ComputationFactory.move movePolicy afterInitialization with
                  | .error _ => none
                  | .ok moved =>
                      let afterMove := moved.result
                      match callPolicyExact : Cpu.policy? loaded afterMove with
                      | none => none
                      | some callPolicy =>
                          match CallFactory.call callPolicy afterMove with
                          | .error _ => none
                          | .ok called =>
                              let binding := WriteFile.CallPolicy.ofFactory callPolicyExact called
                              match GetStdHandle.StackPlanFactory.deriveLoaded? binding with
                              | .error _ => none
                              | .ok stack =>
                                  some (
                                    splice.initialization.entries.length == 1 &&
                                    BitVec.setWidth 32 (afterMove.gpr .rcx) ==
                                      Grass.Platform.Win32.StdHandleId.output.value &&
                                    stack.continuation ==
                                      called.receipt.fetch.site.fallthroughRip &&
                                    stack.returnSlot.provenance ==
                                      called.receipt.storeDescriptor.provenance &&
                                    stack.returnSlot.range == called.receipt.storeDescriptor.range &&
                                    stack.returnSlot.range.size ==
                                      WriteFile.Abi.returnAddressBytes &&
                                    stack.homeSlot.provenance == stack.returnSlot.provenance &&
                                    stack.homeSlot.range.size == Grass.ABI.Win64.shadowSpaceBytes)

private def check (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError "actual Hello GetStdHandle CALL prefix refused")

#eval check (actualPrefix? == some true)

end Grass.Tests.Win32HelloCall
