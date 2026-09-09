import Grass.Assembly.ByteLayout
import Grass.Assembly.SignedRel32
import Grass.Assembly.X86ClosedEncoding
import Grass.Assembly.X86ControlFlow
import Grass.ISA.X86.Rel32

/-! Byte layout and rel32 resolution for source programs containing only closed
instructions and local branches. `Result.origins_exact` and
`Result.branch_position_exact` preserve source provenance and computed byte
positions. This layer assigns no execution meaning to annotations. -/
namespace Grass.Assembly.X86BranchLayout

open Grass.ISA.X86 Grass.Std.Logical X86Source X86ControlFlow
inductive Template where
  | closed (encoding : InsnEncoding)
  | branch (kind : Grass.ISA.X86.Rel32.Kind) (targetIndex : Nat)
deriving Repr, DecidableEq

def Template.size : Template → Nat
  | .closed encoding => encoding.size
  | .branch kind _ => Grass.ISA.X86.Rel32.encodedSize kind

def template? (item : CodeItem) (flow : Flow) : Option Template :=
  match item.instruction.mnemonic, item.instruction.operands, flow with
  | .jmp, [.symbol _], .jump target => some (.branch .jump target)
  | .jz, [.symbol _], .conditional .equal target _ => some (.branch .equal target)
  | .je, [.symbol _], .conditional .equal target _ => some (.branch .equal target)
  | .ja, [.symbol _], .conditional .above target _ => some (.branch .above target)
  | _, _, _ => (Grass.Assembly.X86ClosedEncoding.encode item.instruction).map .closed

def deriveTemplates? : List CodeItem → List Flow → Option (List Template)
  | [], [] => some []
  | item :: items, flow :: flows => do
      let template ← template? item flow
      pure (template :: (← deriveTemplates? items flows))
  | _, _ => none

structure BranchOrigin where
  private mk ::
  kind : Grass.ISA.X86.Rel32.Kind
  sourceIndex : Nat
  targetIndex : Nat
  layoutSizes : List Nat
  sourceOffset : Nat
  targetOffset : Nat
  sourceInBounds : sourceIndex < layoutSizes.length
  targetInBounds : targetIndex < layoutSizes.length
  sourceOffsetExact : sourceOffset = Grass.Assembly.ByteLayout.offset layoutSizes sourceIndex
  targetOffsetExact : targetOffset = Grass.Assembly.ByteLayout.offset layoutSizes targetIndex
  resolved : Grass.Assembly.SignedRel32.Resolved
  resolutionExact : Grass.Assembly.SignedRel32.resolve? sourceOffset (Grass.ISA.X86.Rel32.encodedSize kind) targetOffset = some resolved

inductive Output where
  | closed (origin : CodeItem) (encoding : InsnEncoding)
      (sourceExact : Grass.Assembly.X86ClosedEncoding.encode origin.instruction = some encoding)
  | branch (origin : CodeItem) (info : BranchOrigin)

def Output.encoding : Output → InsnEncoding
  | .closed _ encoding _ => encoding
  | .branch _ info => Grass.ISA.X86.Rel32.encode info.kind info.resolved.bits

def Output.origin : Output → CodeItem
  | .closed origin _ _ | .branch origin _ => origin

def Output.template : Output → Template
  | .closed _ encoding _ => .closed encoding
  | .branch _ info => .branch info.kind info.targetIndex

def Output.branchOrigin? : Output → Option BranchOrigin
  | .closed .. => none
  | .branch _ info => some info

def Output.UsesSizes (sizes : List Nat) : Output → Prop
  | .closed .. => True
  | .branch _ info => info.layoutSizes = sizes

instance (sizes : List Nat) (output : Output) : Decidable (output.UsesSizes sizes) := by
  cases output <;> simp [Output.UsesSizes] <;> infer_instance

def Output.AtIndex (index : Nat) : Output → Prop
  | .closed .. => True
  | .branch _ info => info.sourceIndex = index

instance (index : Nat) (output : Output) : Decidable (output.AtIndex index) := by
  cases output <;> simp [Output.AtIndex] <;> infer_instance

theorem Output.size_eq (output : Output) :
    output.encoding.size = output.template.size := by
  cases output with
  | closed => rfl
  | branch origin info => exact Grass.ISA.X86.Rel32.size_eq info.kind info.resolved.bits

theorem Output.encoding_decodes (output : Output) (rest : ByteSeq) :
    decodeInsn (output.encoding.toBytes ++ rest) = .ok (output.encoding, rest) := by
  cases output with
  | closed origin encoding success => exact Grass.Assembly.X86ClosedEncoding.encode_decodes success rest
  | branch origin info => exact Grass.ISA.X86.Rel32.decode_encode info.kind info.resolved.bits rest

theorem BranchOrigin.target_equation (info : BranchOrigin) :
    (info.targetOffset : Int) = (info.sourceOffset : Int) +
      (Grass.ISA.X86.Rel32.encodedSize info.kind : Int) + info.resolved.bits.toInt :=
  Grass.Assembly.SignedRel32.target_equation_of_resolve? info.resolutionExact

private def resolveFrom (items : List CodeItem) (templates : List Template)
    (sizes : List Nat) : Nat → List CodeItem → List Template → Option (List Output)
  | _, [], [] => some []
  | index, item :: itemTail, template :: templateTail => do
      let output ← match template with
        | .closed encoding =>
          if h : Grass.Assembly.X86ClosedEncoding.encode item.instruction = some encoding then
            some (.closed item encoding h)
          else none
        | .branch kind targetIndex => do
          if hs : index < sizes.length then
            if ht : targetIndex < sizes.length then
              let sourceOffset := Grass.Assembly.ByteLayout.offset sizes index
              let targetOffset := Grass.Assembly.ByteLayout.offset sizes targetIndex
              match h : Grass.Assembly.SignedRel32.resolve? sourceOffset (Grass.ISA.X86.Rel32.encodedSize kind) targetOffset with
              | none => none
              | some resolved => some (.branch item
                  { kind, sourceIndex := index, targetIndex, layoutSizes := sizes,
                    sourceOffset, targetOffset, sourceInBounds := hs, targetInBounds := ht,
                    sourceOffsetExact := rfl, targetOffsetExact := rfl,
                    resolved, resolutionExact := h })
            else none
          else none
      pure (output :: (← resolveFrom items templates sizes (index + 1) itemTail templateTail))
  | _, _, _ => none

structure Result where
  private mk ::
  program : CheckedProgram
  templates : List Template
  outputs : List Output
  templatesExact : deriveTemplates? program.collected.code program.flows = some templates
  outputsExact : resolveFrom program.collected.code templates (templates.map Template.size)
    0 program.collected.code templates = some outputs
  originsExact : outputs.map Output.origin = program.collected.code
  outputTemplatesExact : outputs.map Output.template = templates
  branchesUseSizes : ∀ output ∈ outputs,
    output.UsesSizes (templates.map Template.size)
  branchIndicesExact : ∀ pair ∈ outputs.zipIdx, pair.1.AtIndex pair.2

def layout? (program : CheckedProgram) : Option Result := do
  match ht : deriveTemplates? program.collected.code program.flows with
  | none => none
  | some templates =>
    match h : resolveFrom program.collected.code templates (templates.map Template.size)
        0 program.collected.code templates with
    | none => none
    | some outputs =>
      if ho : outputs.map Output.origin = program.collected.code then
        if ht' : outputs.map Output.template = templates then
          if hs : ∀ output ∈ outputs, output.UsesSizes (templates.map Template.size) then
            if hi : ∀ pair ∈ outputs.zipIdx, pair.1.AtIndex pair.2 then
              some ⟨program, templates, outputs, ht, h, ho, ht', hs, hi⟩
            else none
          else none
        else none
      else none

theorem layout?_program {program : CheckedProgram} {result : Result}
    (success : layout? program = some result) : result.program = program := by
  unfold layout? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  simp at success
  subst result
  rfl

def Result.encodings (result : Result) : List InsnEncoding :=
  result.outputs.map Output.encoding

def Result.sizes (result : Result) : List Nat := result.templates.map Template.size

def Result.totalSize (result : Result) : Nat := result.sizes.sum

theorem Result.origins_exact (result : Result) :
    result.outputs.map Output.origin = result.program.collected.code := result.originsExact

theorem Result.templates_exact (result : Result) :
    result.outputs.map Output.template = result.templates := result.outputTemplatesExact

theorem Result.branch_uses_derived_layout (result : Result) (output : Output)
    (member : output ∈ result.outputs) (info : BranchOrigin)
    (branch : output.branchOrigin? = some info) :
    info.layoutSizes = result.sizes := by
  have uses := result.branchesUseSizes output member
  cases output <;> simp [Output.branchOrigin?, Output.UsesSizes] at branch uses
  subst info
  exact uses

theorem Result.branch_position_exact (result : Result) (output : Output) (index : Nat)
    (member : (output, index) ∈ result.outputs.zipIdx) (info : BranchOrigin)
    (branch : output.branchOrigin? = some info) :
    info.sourceIndex = index ∧
      info.sourceOffset = Grass.Assembly.ByteLayout.offset result.sizes index ∧
      info.targetOffset = Grass.Assembly.ByteLayout.offset result.sizes info.targetIndex := by
  have atIndex := result.branchIndicesExact (output, index) member
  obtain ⟨_, indexBound, outputAt⟩ := List.mem_zipIdx member
  simp at outputAt
  have outputMember : output ∈ result.outputs := by
    rw [outputAt]
    exact List.getElem_mem (by simpa using indexBound)
  have uses := result.branch_uses_derived_layout output outputMember info branch
  cases output <;> simp [Output.branchOrigin?, Output.AtIndex] at branch atIndex
  subst info
  refine ⟨atIndex, ?_, ?_⟩
  · rw [BranchOrigin.sourceOffsetExact, atIndex, uses]
  · rw [BranchOrigin.targetOffsetExact, uses]

theorem Result.branch_target_equation (result : Result) (output : Output) (index : Nat)
    (member : (output, index) ∈ result.outputs.zipIdx) (info : BranchOrigin)
    (branch : output.branchOrigin? = some info) :
    (Grass.Assembly.ByteLayout.offset result.sizes info.targetIndex : Int) =
      (Grass.Assembly.ByteLayout.offset result.sizes index : Int) +
        (Grass.ISA.X86.Rel32.encodedSize info.kind : Int) + info.resolved.bits.toInt := by
  obtain ⟨_, sourceExact, targetExact⟩ :=
    result.branch_position_exact output index member info branch
  rw [← sourceExact, ← targetExact]
  exact info.target_equation

theorem Result.encodingSizes_eq (result : Result) :
    result.encodings.map InsnEncoding.size = result.sizes := by
  simp [Result.encodings, Result.sizes, List.map_map, Function.comp_def,
    ← result.templates_exact, Output.size_eq]

theorem Result.emittedLength_eq_totalSize (result : Result) :
    (Grass.Assembly.ByteLayout.emitted result.encodings).length = result.totalSize := by
  rw [Grass.Assembly.ByteLayout.emitted_length]
  simp only [Grass.Assembly.ByteLayout.sizes, Result.totalSize]
  rw [Result.encodingSizes_eq]

theorem Result.every_encoding_decodes (result : Result) (encoding : InsnEncoding)
    (member : encoding ∈ result.encodings) (rest : ByteSeq) :
    decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest) := by
  obtain ⟨output, member, rfl⟩ := List.mem_map.mp member
  exact output.encoding_decodes rest

theorem Result.branch_target_in_emitted (result : Result) (output : Output)
    (member : output ∈ result.outputs) (info : BranchOrigin)
    (branch : output.branchOrigin? = some info) :
    info.targetOffset < (Grass.Assembly.ByteLayout.emitted result.encodings).length := by
  have sizesExact := result.branch_uses_derived_layout output member info branch
  have bounded : info.targetIndex < result.sizes.length := by
    rw [← sizesExact]
    exact info.targetInBounds
  have allPositive : ∀ size ∈ result.sizes, 0 < size := by
    intro size entry
    rw [← result.encodingSizes_eq] at entry
    obtain ⟨encoding, _, rfl⟩ := List.mem_map.mp entry
    exact encoding.size_pos
  have positive := allPositive _ (List.getElem_mem bounded)
  rw [result.emittedLength_eq_totalSize, info.targetOffsetExact, sizesExact]
  exact Grass.Assembly.ByteLayout.offset_lt_total result.sizes info.targetIndex bounded positive

end Grass.Assembly.X86BranchLayout

