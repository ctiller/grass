import Grass.Assembly.FrameArgument
import Grass.Assembly.FrameLea
import Grass.Assembly.FrameLoad
import Grass.Assembly.FrameStore
import Grass.Assembly.RipRelative
import Grass.Assembly.Win32Constants
import Grass.Assembly.X86BranchLayout

/-! A total, ambiguity-rejecting template boundary for each checked
source instruction. RIP/static/import targets remain symbols; branches retain
checked CFG indices. Hello has 50 retained statements and 42 `CodeItem`s.

Final composition must not prepend `SourcePrologue.generated` to all 42 outputs:
that would duplicate the three authored pushes. It must replace the checked
saved prefix by the generated equivalent prefix plus allocation, insert any
separately proved local initializers at that boundary, and then append outputs
corresponding to `frame.saved.rest`. Branch indices retained here are original
checked-source indices; final layout must translate every index at or beyond the
insertion boundary before resolving branch bytes. The same inserted byte count
shifts body-to-static/import RIP coordinates. Initializer encoding and the
checked splice into final byte-layout coordinates remain separate obligations. -/
namespace Grass.Assembly.SourceTemplates

open Grass.ISA.X86 Grass.ISA.X86.BasicInstructions X86Source X86ControlFlow

inductive BranchSourceKind where
  | jump | zero | equal | above
deriving Repr, DecidableEq

def BranchSourceKind.mnemonic : BranchSourceKind → Mnemonic
  | .jump => .jmp | .zero => .jz | .equal => .je | .above => .ja

def BranchSourceKind.encodingKind : BranchSourceKind → Grass.ISA.X86.Rel32.Kind
  | .jump => .jump | .zero | .equal => .equal | .above => .above

def BranchSourceKind.flow (kind : BranchSourceKind) (targetIndex continuation : Nat) : Flow :=
  match kind with
  | .jump => .jump targetIndex
  | .zero | .equal => .conditional .equal targetIndex continuation
  | .above => .conditional .above targetIndex continuation

inductive Template where
  | encoded (encoding : InsnEncoding)
  | branch (kind : Grass.ISA.X86.Rel32.Kind) (targetIndex : Nat)
  | ripAddress (destination : Gpr) (symbol : String) (prototype : InsnEncoding)
  | ripCall (importSymbol : String) (prototype : InsnEncoding)
  | sizeOf32 (destination : Gpr) (staticSymbol : String) (prototype : InsnEncoding)
deriving Repr, DecidableEq

def Template.size : Template → Nat
  | .encoded encoding => encoding.size
  | .branch kind _ => Grass.ISA.X86.Rel32.encodedSize kind
  | .ripAddress _ _ prototype | .ripCall _ prototype | .sizeOf32 _ _ prototype => prototype.size

inductive Output (frame : SourceFrame.Result) (rootOffset : Nat) where
  | closed (origin : CodeItem) (encoding : InsnEncoding)
      (exact : X86ClosedEncoding.encode origin.instruction = some encoding)
  | store (origin : CodeItem) (resolved : Store32.Resolved)
      (exact : FrameStore.resolve? frame rootOffset origin = some resolved)
  | load (origin : CodeItem) (resolved : FrameLoad.Result)
      (exact : FrameLoad.resolve? frame rootOffset origin = some resolved)
  | lea (origin : CodeItem) (resolved : FrameLea.Result)
      (exact : FrameLea.resolve? frame rootOffset origin = some resolved)
  | argument (origin : CodeItem) (resolved : FrameArgument.Result)
      (exact : FrameArgument.resolve? frame rootOffset origin = some resolved)
  | constant (origin : CodeItem) (resolved : Win32Constants.Result)
      (exact : Win32Constants.resolve? frame origin = some resolved)
  | branch (origin : CodeItem) (sourceFlow : Flow) (kind : BranchSourceKind)
      (label : String) (targetIndex continuation : Nat)
      (instructionExact : origin.instruction = ⟨kind.mnemonic, [.symbol label]⟩)
      (flowExact : sourceFlow = kind.flow targetIndex continuation)
  | ripAddress (origin : CodeItem) (destination : Gpr) (symbol : String)
      (prototype : InsnEncoding)
      (sourceExact : origin.instruction =
        ⟨.lea, [.register ⟨destination, .w64⟩, .ripMemory symbol]⟩)
      (prototypeExact : RipRelative.encode? (.address destination) 0 = some prototype)
  | ripCall (origin : CodeItem) (sourceFlow : Flow) (symbol : String) (continuation : Nat)
      (prototype : InsnEncoding)
      (sourceExact : origin.instruction = ⟨.call, [.ripMemory symbol]⟩)
      (flowExact : sourceFlow = .externalCall symbol continuation)
      (prototypeExact : RipRelative.encode? .indirectCall 0 = some prototype)
  | sizeOf32 (origin : CodeItem) (destination : Gpr) (symbol : String)
      (prototype : InsnEncoding)
      (sourceExact : origin.instruction =
        ⟨.mov, [.register ⟨destination, .w32⟩, .sizeOf symbol]⟩)
      (prototypeExact : X86ClosedEncoding.encode
        ⟨.mov, [.register ⟨destination, .w32⟩, .immediate 0]⟩ = some prototype)

def Output.origin {frame rootOffset} : Output frame rootOffset → CodeItem
  | .closed origin .. | .store origin .. | .load origin .. | .lea origin ..
  | .argument origin .. | .constant origin .. | .branch origin ..
  | .ripAddress origin .. | .ripCall origin .. | .sizeOf32 origin .. => origin

def Output.template {frame rootOffset} : Output frame rootOffset → Template
  | .closed _ encoding _ => .encoded encoding
  | .store _ resolved _ => .encoded resolved.encoding
  | .load _ resolved _ => .encoded resolved.encoding
  | .lea _ resolved _ => .encoded resolved.encoding
  | .argument _ resolved _ => .encoded resolved.encoding
  | .constant _ resolved _ => .encoded resolved.encoding
  | .branch _ _ kind _ target _ _ _ => .branch kind.encodingKind target
  | .ripAddress _ destination symbol prototype .. => .ripAddress destination symbol prototype
  | .ripCall _ _ symbol _ prototype .. => .ripCall symbol prototype
  | .sizeOf32 _ destination symbol prototype .. => .sizeOf32 destination symbol prototype

def Output.sourceFlow? {frame rootOffset} : Output frame rootOffset → Option Flow
  | .branch _ flow .. | .ripCall _ flow .. => some flow
  | _ => none

def relevantFlow? : Flow → Option Flow
  | flow@(.jump _) | flow@(.conditional ..) | flow@(.externalCall ..) => some flow
  | .next _ | .trap => none

private def singletonResolve {frame : SourceFrame.Result} {rootOffset : Nat}
    (item : CodeItem) (flow : Flow) : List (Output frame rootOffset) :=
  let closed := match h : X86ClosedEncoding.encode item.instruction with
    | some encoding => [Output.closed item encoding h] | none => []
  let store := match h : FrameStore.resolve? frame rootOffset item with
    | some result => [Output.store item result h] | none => []
  let load := match h : FrameLoad.resolve? frame rootOffset item with
    | some result => [Output.load item result h] | none => []
  let lea := match h : FrameLea.resolve? frame rootOffset item with
    | some result => [Output.lea item result h] | none => []
  let argument := match h : FrameArgument.resolve? frame rootOffset item with
    | some result => [Output.argument item result h] | none => []
  let constant := match h : Win32Constants.resolve? frame item with
    | some result => [Output.constant item result h] | none => []
  let symbolic : List (Output frame rootOffset) :=
    match hs : item.instruction, hf : flow with
    | ⟨.jmp, [.symbol label]⟩, .jump target =>
        [.branch item flow .jump label target 0 hs hf]
    | ⟨.jz, [.symbol label]⟩, .conditional .equal target continuation =>
        [.branch item flow .zero label target continuation hs hf]
    | ⟨.je, [.symbol label]⟩, .conditional .equal target continuation =>
        [.branch item flow .equal label target continuation hs hf]
    | ⟨.ja, [.symbol label]⟩, .conditional .above target continuation =>
        [.branch item flow .above label target continuation hs hf]
    | ⟨.lea, [.register ⟨destination, .w64⟩, .ripMemory symbol]⟩, _ =>
        match hp : RipRelative.encode? (.address destination) 0 with
        | some prototype => [.ripAddress item destination symbol prototype hs hp]
        | none => []
    | ⟨.call, [.ripMemory symbol]⟩, .externalCall flowSymbol continuation =>
        if same : symbol = flowSymbol then
          match hp : RipRelative.encode? .indirectCall 0 with
          | some prototype => [.ripCall item flow symbol continuation prototype hs
              (by rw [hf, same]) hp]
          | none => []
        else []
    | ⟨.mov, [.register ⟨destination, .w32⟩, .sizeOf symbol]⟩, _ =>
        match hp : X86ClosedEncoding.encode
            ⟨.mov, [.register ⟨destination, .w32⟩, .immediate 0]⟩ with
        | some prototype => [.sizeOf32 item destination symbol prototype hs hp]
        | none => []
    | _, _ => []
  closed ++ store ++ load ++ lea ++ argument ++ constant ++ symbolic

def classify? (frame : SourceFrame.Result) (rootOffset : Nat)
    (item : CodeItem) (flow : Flow) : Option (Output frame rootOffset) :=
  match singletonResolve item flow with
  | [output] => some output
  | _ => none

def candidateCount (frame : SourceFrame.Result) (rootOffset : Nat)
    (item : CodeItem) (flow : Flow) : Nat :=
  (singletonResolve (frame := frame) (rootOffset := rootOffset) item flow).length

def classifyAll? (frame : SourceFrame.Result) (rootOffset : Nat) :
    List CodeItem → List Flow → Option (List (Output frame rootOffset))
  | [], [] => some []
  | item :: items, flow :: flows => do
      let output ← classify? frame rootOffset item flow
      pure (output :: (← classifyAll? frame rootOffset items flows))
  | _, _ => none

structure Result (frame : SourceFrame.Result) (rootOffset : Nat) where
  private mk ::
  outputs : List (Output frame rootOffset)
  outputsExact : classifyAll? frame rootOffset frame.program.collected.code frame.program.flows =
    some outputs
  originsExact : outputs.map Output.origin = frame.program.collected.code
  sourceFlowsAtIndex : ∀ pair ∈ outputs.zipIdx,
    pair.1.sourceFlow? = (frame.program.flows[pair.2]?).bind relevantFlow?

def derive? (frame : SourceFrame.Result) (rootOffset : Nat) : Option (Result frame rootOffset) := do
  match h : classifyAll? frame rootOffset frame.program.collected.code frame.program.flows with
  | none => none
  | some outputs =>
    if origins : outputs.map Output.origin = frame.program.collected.code then
      if flows : ∀ pair ∈ outputs.zipIdx,
          pair.1.sourceFlow? = (frame.program.flows[pair.2]?).bind relevantFlow? then
        some ⟨outputs, h, origins, flows⟩
      else none
    else none

theorem Result.origin_order {frame rootOffset} (result : Result frame rootOffset) :
    result.outputs.map Output.origin = frame.program.collected.code := result.originsExact

theorem Result.output_count {frame rootOffset} (result : Result frame rootOffset) :
    result.outputs.length = frame.program.collected.code.length := by
  rw [← result.originsExact, List.length_map]

theorem Result.source_flow_at {frame rootOffset} (result : Result frame rootOffset)
    (output : Output frame rootOffset) (index : Nat)
    (member : (output, index) ∈ result.outputs.zipIdx) :
    output.sourceFlow? = (frame.program.flows[index]?).bind relevantFlow? :=
  result.sourceFlowsAtIndex (output, index) member

def Result.sizes {frame rootOffset} (result : Result frame rootOffset) : List Nat :=
  result.outputs.map (fun output => output.template.size)

end Grass.Assembly.SourceTemplates
