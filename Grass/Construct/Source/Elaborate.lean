import Grass.Construct.Source.Alpha
import Grass.Construct.Source.Manifest

/-!
# Checked authored-source elaboration core

`elaborate` composes hygienic label normalization, structural CFG closure, and
manifest derivation. Its result carries the exact normalized AST and the exact
manifest projected from that AST. This is the term-level core for a later
command/parser frontend; it does not parse syntax or prove instruction semantics.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x

/-- Structurally closed authored AST paired with its exact derived manifest. -/
structure ElaboratedSource
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x}
    (source : PreAlphaAst State Terminal Instruction Annotation)
    (model : LabelAlphaModel) where
  authored : Ast State Terminal Instruction Annotation
  manifest : Manifest Terminal
  authoredExact : authored = source.alphaNormalize model
  manifestExact : manifest = authored.manifest
  structural : authored.WellFormed

namespace ElaboratedSource

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}
  {source : PreAlphaAst State Terminal Instruction Annotation}
  {model : LabelAlphaModel}

/-- `instructionsExact` ties the result to the exact pre-alpha instruction list. -/
theorem instructionsExact (elaborated : ElaboratedSource source model) :
    (elaborated.authored.blocks.flatMap fun block => block.body.expand) =
      source.instructions := by
  rw [elaborated.authoredExact]
  exact source.alphaNormalize_instructions model

/-- `annotationsExact` ties every result annotation list to its pre-alpha block. -/
theorem annotationsExact (elaborated : ElaboratedSource source model) :
    elaborated.authored.blocks.map Block.annotations =
      source.blocks.map PreAlphaBlock.annotations := by
  rw [elaborated.authoredExact]
  exact source.alphaNormalize_annotations model

/-- `manifestEntryExact` exposes the exact normalized entry identity. -/
theorem manifestEntryExact (elaborated : ElaboratedSource source model) :
    elaborated.manifest.entry = source.entry.alphaNormalize model := by
  rw [elaborated.manifestExact, elaborated.authoredExact]
  rfl

/-- `manifestBlockIdsExact` exposes the exact normalized block identities. -/
theorem manifestBlockIdsExact (elaborated : ElaboratedSource source model) :
    elaborated.manifest.blockIds = elaborated.authored.blockIds := by
  rw [elaborated.manifestExact]
  exact elaborated.authored.manifest_blockIds

/-- `manifestInstructionCountExact` ties manifest size to exact authored size. -/
theorem manifestInstructionCountExact
    (elaborated : ElaboratedSource source model) :
    elaborated.manifest.instructionCount = elaborated.authored.instructionCount := by
  rw [elaborated.manifestExact]
  exact elaborated.authored.manifest_instructionCount

end ElaboratedSource

/--
Normalize labels, reject a structurally open graph, and derive its exact manifest.

Instruction-local correctness and platform verification remain later phases.
-/
def elaborate {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x}
    (source : PreAlphaAst State Terminal Instruction Annotation)
    (model : LabelAlphaModel) :
    Except AlphaError (ElaboratedSource source model) :=
  match checkAlpha source model with
  | .error error => .error error
  | .ok normalized =>
      .ok ⟨normalized.authored, normalized.authored.manifest,
        normalized.authoredExact, rfl, normalized.structural⟩

end Grass.Construct.Source
