import Grass.Core.Identifiers

/-!
# Hierarchical finite fragment source

Literal instructions, generated bodies, and nested sequences share one source
tree.  Expansion is a structural fold over that tree, so generated instructions
remain inspectable and no parallel flattened listing is authored.
-/

namespace Grass.Construct.Fragment

universe u

/-- Stable identity of one fragment-constructor application. -/
structure FragmentId where
  id : StableId
deriving Repr, DecidableEq, Hashable

/-- Finite hierarchical source over an open instruction type. -/
inductive Source (Instruction : Type u) where
  | literal (instructions : List Instruction)
  | generated (id : FragmentId) (body : Source Instruction)
  | sequence (children : List (Source Instruction))
deriving Repr

namespace Source

variable {Instruction : Type u}

/-- Exact flat instruction expansion in structural source order. -/
def expand : Source Instruction → List Instruction
  | .literal instructions => instructions
  | .generated _ body => body.expand
  | .sequence children => children.flatMap expand

/-- Number of literal leaves in the hierarchy. -/
def leafCount : Source Instruction → Nat
  | .literal _ => 1
  | .generated _ body => body.leafCount
  | .sequence children => (children.map leafCount).sum

/-- Number of instructions in the exact expansion. -/
def instructionCount (source : Source Instruction) : Nat := source.expand.length

@[simp] theorem expand_literal (instructions : List Instruction) :
    (Source.literal instructions).expand = instructions := by simp [expand]

@[simp] theorem expand_generated (id : FragmentId) (body : Source Instruction) :
    (Source.generated id body).expand = body.expand := by simp [expand]

@[simp] theorem expand_sequence (children : List (Source Instruction)) :
    (Source.sequence children).expand = children.flatMap expand := by simp [expand]

@[simp] theorem leafCount_literal (instructions : List Instruction) :
    (Source.literal instructions).leafCount = 1 := by simp [leafCount]

@[simp] theorem leafCount_generated (id : FragmentId)
    (body : Source Instruction) :
    (Source.generated id body).leafCount = body.leafCount := by simp [leafCount]

@[simp] theorem leafCount_sequence (children : List (Source Instruction)) :
    (Source.sequence children).leafCount = (children.map leafCount).sum := by
  simp [leafCount]

@[simp] theorem instructionCount_literal (instructions : List Instruction) :
    (Source.literal instructions).instructionCount = instructions.length := by
  simp [instructionCount]

@[simp] theorem instructionCount_generated (id : FragmentId)
    (body : Source Instruction) :
    (Source.generated id body).instructionCount = body.instructionCount := by
  simp [instructionCount]

/-- Wrapping a body as a named generator application changes hierarchy but not
its exact instruction expansion. -/
theorem generated_expansion_exact (id : FragmentId) (body : Source Instruction) :
    (Source.generated id body).expand = body.expand := by simp

end Source

end Grass.Construct.Fragment
