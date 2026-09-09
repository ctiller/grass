import Grass.Assembly.SourceFrameHeader
import Grass.Assembly.SavedPrefix
import Grass.Assembly.SourceStore
import Grass.Platform.Win32.Signatures

/-! Source-derived inputs to the Win64 frame calculation. `Result.layout`
uses the parsed locals, checked saved prefix, and resolved API signature.
This module does not insert allocation or initialization instructions. -/
namespace Grass.Assembly.SourceFrame

open Grass.ABI.Win64 Grass.Platform.Win32.Signatures X86ControlFlow

def callFits (capacity : Nat) : Flow → Bool
  | .externalCall symbol _ => match resolveImport? symbol with
    | none => false
    | some api => decide (argumentCount api ≤ capacity)
  | .next _ | .jump _ | .conditional _ _ _ | .trap => true

structure Result where
  private mk ::
  body : SourceInput.Body
  header : SourceFrameHeader.Header
  statements : List X86Source.LocatedStatement
  program : CheckedProgram
  saved : SavedPrefix.Result
  api : Api
  headerExact : SourceFrameHeader.parse? body = some header
  statementsExact : X86Source.parseBody body = .ok statements
  programExact : X86ControlFlow.check? statements = some program
  savedExact : SavedPrefix.extract? program = some saved
  apiExact : resolveName? header.callFrameName = some api
  callsCovered : ∀ flow ∈ program.flows, callFits (argumentCount api) flow = true

def derive? (body : SourceInput.Body) : Option Result := do
  match hh : SourceFrameHeader.parse? body with
  | none => none
  | some header =>
    match hs : X86Source.parseBody body with
    | .error _ => none
    | .ok statements =>
      match hp : X86ControlFlow.check? statements with
      | none => none
      | some program =>
        match hv : SavedPrefix.extract? program with
        | none => none
        | some saved =>
          match ha : resolveName? header.callFrameName with
          | none => none
          | some api =>
            if hc : ∀ flow ∈ program.flows, callFits (argumentCount api) flow = true then
              some ⟨body, header, statements, program, saved, api, hh, hs, hp, hv, ha, hc⟩
            else none

def Result.slots (result : Result) : List String :=
  result.header.locals.map SourceFrameHeader.Local.name

def Result.layout (result : Result) : CallFrameLayout :=
  SourceStore.frameForSlots (argumentCount result.api) result.saved.registers result.slots

theorem derive?_body {body : SourceInput.Body} {result : Result}
    (success : derive? body = some result) : result.body = body := by
  unfold derive? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  rfl

theorem Result.layout_arguments (result : Result) :
    result.layout.argumentCount = (parameters result.api).length := rfl

theorem Result.layout_saved (result : Result) :
    result.layout.savedRegisters = result.saved.registers := rfl

theorem Result.layout_locals (result : Result) :
    result.layout.localBytes = result.header.locals.length * 4 := by
  simp [Result.layout, Result.slots, SourceStore.frameForSlots]

theorem Result.saved_program (result : Result) : result.saved.program = result.program :=
  SavedPrefix.extract?_program result.savedExact

theorem Result.layout_admissible (result : Result) : result.layout.Admissible := by
  change 0 < 4 ∧ stackAlignment % 4 = 0
  decide

theorem Result.call_arity_bounded (result : Result) (symbol : String) (continuation : Nat)
    (member : Flow.externalCall symbol continuation ∈ result.program.flows)
    (called : Api) (resolved : resolveImport? symbol = some called) :
    argumentCount called ≤ result.layout.argumentCount := by
  have covered := result.callsCovered _ member
  simpa [callFits, resolved, Result.layout, SourceStore.frameForSlots] using covered

end Grass.Assembly.SourceFrame
