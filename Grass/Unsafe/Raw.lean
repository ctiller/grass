import Grass.Construct.Fragment.Verified

/-!
# Raw instruction construction boundary

`RawHierarchy` is deliberately proof-free: callers may construct arbitrary raw
instructions and concatenate them.  `RawHierarchy.ofVerified` only erases a
verified fragment to its exact expanded instructions; no function in this
module converts raw input back into verification evidence.
-/

namespace Grass.Unsafe

open Grass.CFG Grass.Construct.Fragment

universe u v w

/-- Recursively concatenated raw instruction hierarchy consumed by unsafe
adapters and artifact writers. -/
inductive RawHierarchy (Instruction : Type u) where
  | empty
  | leaf (instructions : List Instruction)
  | append (left right : RawHierarchy Instruction)
deriving Repr

namespace RawHierarchy

variable {Instruction : Type u}

/-- Build an n-ary raw hierarchy over the binary core. -/
def concat (children : List (RawHierarchy Instruction)) : RawHierarchy Instruction :=
  children.foldr RawHierarchy.append .empty

/-- Exact recursively concatenated writer input. -/
def flatten : RawHierarchy Instruction → List Instruction
  | .empty => []
  | .leaf instructions => instructions
  | .append left right => left.flatten ++ right.flatten

@[simp] theorem flatten_empty : (RawHierarchy.empty : RawHierarchy Instruction).flatten = [] := rfl

@[simp] theorem flatten_leaf (instructions : List Instruction) :
    (RawHierarchy.leaf instructions).flatten = instructions := rfl

@[simp] theorem flatten_append (left right : RawHierarchy Instruction) :
    (RawHierarchy.append left right).flatten = left.flatten ++ right.flatten := rfl

@[simp] theorem flatten_concat (children : List (RawHierarchy Instruction)) :
    (RawHierarchy.concat children).flatten = children.flatMap flatten := by
  induction children with
  | nil => rfl
  | cons child rest ih =>
      change child.flatten ++ (RawHierarchy.concat rest).flatten =
        child.flatten ++ rest.flatMap flatten
      rw [ih]

/-- Erase one verified fragment to a raw leaf with exactly its selected source
expansion. -/
def ofVerified {State : Type v} {Effect : Type w}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    {contract : BlockContract State}
    (fragment : VerifiedFragment semantics effectModel contract) :
    RawHierarchy Instruction :=
  .leaf fragment.source.expand

@[simp] theorem flatten_ofVerified {State : Type v} {Effect : Type w}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    {contract : BlockContract State}
    (fragment : VerifiedFragment semantics effectModel contract) :
    (RawHierarchy.ofVerified fragment).flatten = fragment.source.expand := rfl

end RawHierarchy

end Grass.Unsafe
