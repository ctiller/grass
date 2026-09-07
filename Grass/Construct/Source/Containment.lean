import Grass.Construct.Source.Ast

/-!
# Proof-only containment annotations

Containment metadata names one exact authored CFG edge or the exact final
instruction origin of a block. Each annotation carries a violation class and an
affine return envelope. Attachment checking is structural only; interpreting a
class or proving the envelope belongs to later semantic verification.

`Ast.eraseContainment` removes all metadata, and its projection theorems show
that neither the CFG nor any instruction expansion changes.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x y

/-- Finite affine family `base + index * step`, interpreted by a later domain. -/
structure AffineReturnEnvelope (Value : Type x) where
  base : Value
  step : Value
  count : Nat
deriving Repr, DecidableEq

/-- Exact literal source site to which containment metadata is attached. -/
inductive ContainmentSite (Terminal : Type v) where
  | edge (exit : ExitTag) (target : EdgeTarget Terminal)
  | tail (origin : SourceOrigin)
deriving Repr, DecidableEq

/-- Proof-only class and return envelope for one exact authored site. -/
structure ContainmentAnnotation (Terminal : Type v) (Violation : Type x)
    (Value : Type y) where
  site : ContainmentSite Terminal
  violation : Violation
  returns : AffineReturnEnvelope Value
deriving Repr, DecidableEq

namespace ContainmentSite

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Violation : Type x} {Value : Type y} [DecidableEq Terminal]

/-- Whether a site denotes an exact outgoing edge or exact final instruction. -/
def attachedTo (site : ContainmentSite Terminal)
    (block : Block State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) : Bool :=
  match site with
  | .edge exit target => block.cfg.outgoing.contains ⟨exit, target⟩
  | .tail origin =>
      block.body.expandLocated.getLast?.map LocatedInstruction.origin == some origin

end ContainmentSite

namespace Block

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Violation : Type x} {Value : Type y} [DecidableEq Terminal]

/-- Containment sites in authored annotation order. -/
def containmentSites
    (block : Block State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) :
    List (ContainmentSite Terminal) :=
  block.annotations.map ContainmentAnnotation.site

/-- Structural containment metadata has unique sites and every site is attached. -/
def containmentWellFormed
    (block : Block State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) : Bool :=
  decide block.containmentSites.Nodup &&
    block.annotations.all fun annotation => annotation.site.attachedTo block

/-- Certificate-facing statement for `Block.containmentWellFormed`. -/
def ContainmentWellFormed
    (block : Block State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) : Prop :=
  block.containmentWellFormed = true

instance
    (block : Block State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) :
    Decidable block.ContainmentWellFormed :=
  inferInstanceAs (Decidable (block.containmentWellFormed = true))

end Block

namespace Ast

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Violation : Type x} {Value : Type y}

/-- Every block's containment metadata is structurally attached and unique. -/
def ContainmentWellFormed
    [DecidableEq Terminal]
    (source : Ast State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) : Prop :=
  source.blocks.all Block.containmentWellFormed = true

instance
    [DecidableEq Terminal]
    (source : Ast State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) :
    Decidable source.ContainmentWellFormed :=
  inferInstanceAs (Decidable (source.blocks.all Block.containmentWellFormed = true))

private def eraseContainmentBlock
    (block : Block State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) :
    Block State Terminal Instruction Unit :=
  ⟨block.cfg, block.body, []⟩

/-- Remove proof-only containment metadata from an authored source. -/
def eraseContainment
    (source : Ast State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) :
    Ast State Terminal Instruction Unit :=
  ⟨source.entry, source.blocks.map eraseContainmentBlock⟩

/-- `eraseContainment_toGraph` proves metadata erasure leaves the CFG unchanged. -/
@[simp] theorem eraseContainment_toGraph
    (source : Ast State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) :
    source.eraseContainment.toGraph = source.toGraph := by
  simp [eraseContainment, eraseContainmentBlock, Ast.toGraph]

/--
`eraseContainment_expandedBlocks` proves metadata erasure leaves every exact
instruction expansion and structural source origin unchanged.
-/
@[simp] theorem eraseContainment_expandedBlocks
    (source : Ast State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) :
    source.eraseContainment.expandedBlocks = source.expandedBlocks := by
  simp [eraseContainment, eraseContainmentBlock, Ast.expandedBlocks]

private theorem eraseContainmentBlocks_instructionCount
    (blocks : List (Block State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value))) :
    ((blocks.map eraseContainmentBlock).map fun block =>
      block.body.instructionCount).sum =
      (blocks.map fun block => block.body.instructionCount).sum := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [show (eraseContainmentBlock block).body.instructionCount =
        block.body.instructionCount from rfl]
      exact congrArg (fun total => block.body.instructionCount + total)
        (by simpa only [List.map_map] using ih)

/-- `eraseContainment_instructionCount` proves metadata erasure preserves size. -/
@[simp] theorem eraseContainment_instructionCount
    (source : Ast State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) :
    source.eraseContainment.instructionCount = source.instructionCount := by
  exact eraseContainmentBlocks_instructionCount source.blocks

end Ast

/-- Exact reason a containment annotation set is structurally rejected. -/
inductive ContainmentError (Terminal : Type v) where
  | duplicateSites (block : BlockId) (sites : List (ContainmentSite Terminal))
  | unattached (block : BlockId) (site : ContainmentSite Terminal)
deriving Repr, DecidableEq

private def firstContainmentError {State : Type u} {Terminal : Type v}
    {Instruction : Type w} {Violation : Type x} {Value : Type y}
    [DecidableEq Terminal] :
    List (Block State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) →
      Option (ContainmentError Terminal)
  | [] => none
  | block :: rest =>
      if block.containmentSites.Nodup then
        match block.annotations.find? fun annotation =>
            !annotation.site.attachedTo block with
        | some annotation => some (.unattached block.cfg.id annotation.site)
        | none => firstContainmentError rest
      else
        some (.duplicateSites block.cfg.id block.containmentSites)

private theorem firstContainmentError_eq_none {State : Type u}
    {Terminal : Type v} {Instruction : Type w} {Violation : Type x}
    {Value : Type y} [DecidableEq Terminal]
    (blocks : List (Block State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)))
    (noError : firstContainmentError blocks = none) :
    blocks.all Block.containmentWellFormed = true := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      rw [firstContainmentError] at noError
      split at noError
      next unique =>
        split at noError
        next annotation found => contradiction
        next notFound =>
          simp only [List.all_cons, Bool.and_eq_true]
          constructor
          · simp only [Block.containmentWellFormed, unique]
            simpa [List.find?_eq_none] using notFound
          · exact ih noError
      next notUnique => contradiction

/-- Authored source carrying checked, structurally exact containment metadata. -/
structure CheckedContainment {State : Type u} {Terminal : Type v}
    {Instruction : Type w} {Violation : Type x} {Value : Type y}
    [DecidableEq Terminal]
    (authored : Ast State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) where
  source : Ast State Terminal Instruction
    (ContainmentAnnotation Terminal Violation Value)
  sourceExact : source = authored
  valid : source.ContainmentWellFormed

/-- Check annotation uniqueness and exact attachment without changing source. -/
def checkContainment {State : Type u} {Terminal : Type v}
    {Instruction : Type w} {Violation : Type x} {Value : Type y}
    [DecidableEq Terminal]
    (source : Ast State Terminal Instruction
      (ContainmentAnnotation Terminal Violation Value)) :
    Except (ContainmentError Terminal) (CheckedContainment source) :=
  match errorExact : firstContainmentError source.blocks with
  | some error => .error error
  | none =>
      .ok ⟨source, rfl, firstContainmentError_eq_none source.blocks errorExact⟩

end Grass.Construct.Source
