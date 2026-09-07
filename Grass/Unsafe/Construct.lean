import Grass.Unsafe.Raw

/-!
# Explicitly tainted raw construction

`RawConstruction` pairs an unchecked hierarchy with a nonempty taint ledger.
Its constructors preserve the ledger, while `RawConstruction.erase` only
returns `RawHierarchy`; this module defines no operation that manufactures a
Construct certificate from raw data.
-/

namespace Grass.Unsafe

universe u

/-- Why unchecked instructions entered a raw construction. -/
inductive TaintReason where
  | literal
  | generatedUnchecked
  | imported
deriving Repr, DecidableEq

/-- One reviewable unchecked-construction ledger entry. -/
structure Taint where
  source : String
  reason : TaintReason
deriving Repr, DecidableEq

/-- Raw hierarchy with at least one explicit taint entry. -/
structure RawConstruction (Instruction : Type u) where
  raw : RawHierarchy Instruction
  taints : List Taint
  tainted : taints ≠ []

namespace RawConstruction

variable {Instruction : Type u}

/-- Construct one unchecked raw leaf with its required taint. -/
def leaf (taint : Taint) (instructions : List Instruction) :
    RawConstruction Instruction where
  raw := .leaf instructions
  taints := [taint]
  tainted := by simp

/-- Concatenate unchecked constructions while preserving both taint ledgers. -/
def append (left right : RawConstruction Instruction) : RawConstruction Instruction where
  raw := .append left.raw right.raw
  taints := left.taints ++ right.taints
  tainted := by
    cases leftTaints : left.taints with
    | nil => exact False.elim (left.tainted leftTaints)
    | cons head rest => simp

/-- Forget the taint ledger at the visibly unsafe raw boundary. -/
def erase (construction : RawConstruction Instruction) : RawHierarchy Instruction :=
  construction.raw

@[simp] theorem flatten_leaf (taint : Taint) (instructions : List Instruction) :
    (leaf taint instructions).erase.flatten = instructions := rfl

@[simp] theorem flatten_append (left right : RawConstruction Instruction) :
    (append left right).erase.flatten = left.erase.flatten ++ right.erase.flatten := rfl

@[simp] theorem taints_append (left right : RawConstruction Instruction) :
    (append left right).taints = left.taints ++ right.taints := rfl

end RawConstruction

end Grass.Unsafe
