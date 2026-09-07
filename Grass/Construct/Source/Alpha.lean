import Grass.Construct.Source.Ast
import Grass.Construct.Source.Label

/-!
# Alpha-normalized authored CFG surface

`PreAlphaAst` admits literal stable labels and hygienic macro-local labels at
entries, block declarations, and direct edges. `PreAlphaAst.alphaNormalize`
resolves all three positions through one `LabelAlphaModel`, preserving exact
instruction bodies and annotations. `checkAlpha` then requires structural
closure of the resulting ordinary authored `Ast`.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x

/-- Control-flow target before local labels receive stable manifest IDs. -/
inductive PreAlphaTarget (Terminal : Type v) where
  | label (target : AuthoredLabel)
  | terminal (disposition : Terminal)
deriving Repr, DecidableEq

namespace PreAlphaTarget

variable {Terminal : Type v}

/-- Resolve a pre-alpha target to an ordinary stable CFG target. -/
def alphaNormalize (model : LabelAlphaModel) :
    PreAlphaTarget Terminal → EdgeTarget Terminal
  | .label target => .block (target.alphaNormalize model)
  | .terminal disposition => .terminal disposition

end PreAlphaTarget

/-- One named outgoing edge before local-label alpha-normalization. -/
structure PreAlphaEdge (Terminal : Type v) where
  exit : ExitTag
  target : PreAlphaTarget Terminal
deriving Repr, DecidableEq

namespace PreAlphaEdge

variable {Terminal : Type v}

/-- Resolve one edge without changing its exact exit identity. -/
def alphaNormalize (model : LabelAlphaModel) (edge : PreAlphaEdge Terminal) :
    Edge Terminal :=
  ⟨edge.exit, edge.target.alphaNormalize model⟩

end PreAlphaEdge

/-- One authored block declaration before local-label alpha-normalization. -/
structure PreAlphaBlock (State : Type u) (Terminal : Type v)
    (Instruction : Type w) (Annotation : Type x) where
  label : AuthoredLabel
  contract : BlockContract State
  outgoing : List (PreAlphaEdge Terminal)
  body : Fragment.Source Instruction
  annotations : List Annotation

namespace PreAlphaBlock

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- Resolve a pre-alpha block to one ordinary authored block. -/
def alphaNormalize (model : LabelAlphaModel)
    (block : PreAlphaBlock State Terminal Instruction Annotation) :
    Block State Terminal Instruction Annotation where
  cfg :=
    ⟨block.label.alphaNormalize model, block.contract,
      block.outgoing.map fun edge => edge.alphaNormalize model⟩
  body := block.body
  annotations := block.annotations

@[simp] theorem alphaNormalize_body (model : LabelAlphaModel)
    (block : PreAlphaBlock State Terminal Instruction Annotation) :
    (block.alphaNormalize model).body = block.body := rfl

@[simp] theorem alphaNormalize_annotations (model : LabelAlphaModel)
    (block : PreAlphaBlock State Terminal Instruction Annotation) :
    (block.alphaNormalize model).annotations = block.annotations := rfl

end PreAlphaBlock

/-- Complete authored source before hygienic labels receive stable identities. -/
structure PreAlphaAst (State : Type u) (Terminal : Type v)
    (Instruction : Type w) (Annotation : Type x) where
  entry : AuthoredLabel
  blocks : List (PreAlphaBlock State Terminal Instruction Annotation)

namespace PreAlphaAst

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- Exact flat instruction sequence in pre-alpha block order. -/
def instructions (source : PreAlphaAst State Terminal Instruction Annotation) :
    List Instruction :=
  source.blocks.flatMap fun block => block.body.expand

/-- Resolve entry, block, and direct-edge labels through one alpha model. -/
def alphaNormalize (source : PreAlphaAst State Terminal Instruction Annotation)
    (model : LabelAlphaModel) : Ast State Terminal Instruction Annotation where
  entry := source.entry.alphaNormalize model
  blocks := source.blocks.map fun block => block.alphaNormalize model

@[simp] theorem alphaNormalize_entry
    (source : PreAlphaAst State Terminal Instruction Annotation)
    (model : LabelAlphaModel) :
    (source.alphaNormalize model).entry = source.entry.alphaNormalize model := rfl

/-- `alphaNormalize_instructions` proves alpha-normalization never rewrites source. -/
@[simp] theorem alphaNormalize_instructions
    (source : PreAlphaAst State Terminal Instruction Annotation)
    (model : LabelAlphaModel) :
    ((source.alphaNormalize model).blocks.flatMap fun block => block.body.expand) =
      source.instructions := by
  unfold alphaNormalize instructions
  induction source.blocks with
  | nil => rfl
  | cons block rest ih => simp [ih]

/-- `alphaNormalize_annotations` proves review metadata is preserved per block. -/
@[simp] theorem alphaNormalize_annotations
    (source : PreAlphaAst State Terminal Instruction Annotation)
    (model : LabelAlphaModel) :
    (source.alphaNormalize model).blocks.map Block.annotations =
      source.blocks.map PreAlphaBlock.annotations := by
  simp [alphaNormalize]

end PreAlphaAst

/-- Structurally closed alpha-normalization result retaining its exact source. -/
structure AlphaNormalized
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x}
    (source : PreAlphaAst State Terminal Instruction Annotation)
    (model : LabelAlphaModel) where
  authored : Ast State Terminal Instruction Annotation
  authoredExact : authored = source.alphaNormalize model
  structural : authored.WellFormed

/-- Structural diagnostics for a failed alpha-normalization closure check. -/
structure AlphaError where
  entry : BlockId
  blockIds : List BlockId
  unresolvedTargets : List BlockId
deriving Repr, DecidableEq

/-- Normalize every label and require closure of the resulting authored CFG. -/
def checkAlpha
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x}
    (source : PreAlphaAst State Terminal Instruction Annotation)
    (model : LabelAlphaModel) :
    Except AlphaError (AlphaNormalized source model) :=
  let authored := source.alphaNormalize model
  if structural : authored.WellFormed then
    .ok ⟨authored, rfl, structural⟩
  else
    .error ⟨authored.entry, authored.blockIds,
      authored.toGraph.unresolvedTargets⟩

end Grass.Construct.Source
