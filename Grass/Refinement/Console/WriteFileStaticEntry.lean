import Grass.Refinement.Console.WriteFileCountEntry
import Grass.Refinement.Console.WriteFileStaticArgument

/-! Invoke the actual call-entry checker with a source-bound static suffix and
the canonical count local. Static-object/image/current-memory correspondence is
checked here; whole source-code emission correspondence remains an outer proof. -/

namespace Grass.Refinement.Console.WriteFileStaticEntry

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.Semantics
open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {table : StaticObjects.Table} {layout : StaticSection.Layout table} {sectionIndex : Nat}
  (objectBinding : SourceStaticBindings.Binding image.plan layout sectionIndex)
  (before : ExecutionState.State ApiRequest)
  {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
  (call : CallNormal before.machine afterFetch afterTarget afterCall displacement)
  (binding : CallPolicy loaded call) (ready : before.ControlConsistent)
  (evaluated : Raw.EvaluatedCall loaded before call)
  {frame : SourceFrame.Result} {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset}
  (selectedLocal : SourceResolve.LoadSelection source)
  (cut : OutputCut objectBinding.object.declaration.bytes) (fifth : Argument) (provider : ContextId)

/-- Compose both existing checked producers on the same actual post-CALL memory.
The dependent pair retains their original outputs and successful equations. -/
def prepare? : Option
    (Σ prepared : LoadedStaticArgument.Prepared objectBinding loaded call.result.machine.memory cut.offset,
      { entered : CallHandoff loaded before call
          (WriteFileStaticArgument.requestOf call.result prepared
            (WriteFileCountArgument.argument binding.policy call selectedLocal)) provider //
        LoadedStaticArgument.prepare? objectBinding loaded call.result.machine.memory cut.offset = some prepared ∧
        WriteFileCountEntry.prepareCountCall? before call binding ready evaluated selectedLocal
          prepared.argument prepared.bytes fifth provider = some entered ∧
        SourceResolve.static? source.symbols objectBinding.name = some objectBinding.sourceSymbol }) :=
  if sourceBinding : SourceResolve.static? source.symbols objectBinding.name = some objectBinding.sourceSymbol then
    match _preparedEq : LoadedStaticArgument.prepare? objectBinding loaded call.result.machine.memory cut.offset with
    | none => none
    | some prepared =>
        match enteredEq : WriteFileCountEntry.prepareCountCall? before call binding ready evaluated selectedLocal
            prepared.argument prepared.bytes fifth provider with
        | none => none
        | some entered => some ⟨prepared, entered, rfl, enteredEq, sourceBinding⟩
  else none

/-- The actual request sent through the composed entry has this object's exact
remaining bytes and initialized input at the actual post-CALL state. -/
theorem request_remaining
    (prepared : LoadedStaticArgument.Prepared objectBinding loaded call.result.machine.memory cut.offset)
    (entered : CallHandoff loaded before call
      (WriteFileStaticArgument.requestOf call.result prepared
        (WriteFileCountArgument.argument binding.policy call selectedLocal)) provider) :
    entered.handoff.record.request.bytes = cut.remaining ∧
      entered.handoff.record.request.buffer = prepared.argument ∧
      InputMatches call.result.machine.memory entered.handoff.record.request :=
  ⟨prepared.bytesExact, rfl, WriteFileStaticArgument.requestOf_input _ _ _⟩

/-- Continue the existing same-call return/body proof with the exact handoff
returned by this producer. The remaining inputs are its actual service history,
return, checked resume, source body, and reached cursor. -/
abbrev returned_body
    {R Status : Type} [Grass.Resource.ResourceModel R] {resources : R}
    {spec : Grass.SpecProcess resources}
    {projection : Grass.Console.CapturedTargetProjection spec Status}
    {result}
    (_ran : prepare? objectBinding before call binding ready evaluated selectedLocal cut fifth provider = some result) :=
  WriteFileCountEntry.returned_body (projection := projection) selectedLocal binding ready evaluated
    result.1.argument result.1.bytes fifth result.2.val result.2.property.2.1

end Grass.Refinement.Console.WriteFileStaticEntry
