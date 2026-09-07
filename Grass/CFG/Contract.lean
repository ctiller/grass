import Grass.Core.Identifiers

/-!
# CFG block contracts

The ISA-neutral contract vocabulary used by construction and lowering.

A contract states an entry predicate and a finite, named family of exit
predicates.  It does not identify machine instructions, guess which exits an
instruction has, or confer proof authority on generated code.  Later checkers
must prove that an implementation establishes one declared exit predicate for
every machine outcome it admits.
-/

namespace Grass.CFG

universe u

/-- Stable identity of one closed, alpha-normalized basic block.

This is the manifest identity after elaboration.  Hygienic macro-local labels
are minted as opaque construction tokens and receive a `BlockId` only during
alpha-normalization; this type is not the macro label-minting API.
-/
structure BlockId where
  id : StableId
deriving Repr, DecidableEq, Hashable

/-- Stable identity of one exit from a block contract.

Exit tags are scoped by their containing block contract, so conventional tags
such as `normal` may occur in many blocks without becoming the same CFG edge.
-/
structure ExitTag where
  id : StableId
deriving Repr, DecidableEq, Hashable

/-- The postcondition associated with one named exit. -/
structure ExitContract (State : Type u) where
  tag : ExitTag
  ensures : State → Prop

/-- A block's logical entry condition and complete authored exit family.

`exits` is data so graph discovery and diagnostics can enumerate it.  Duplicate
tags are rejected by `BlockContract.wellFormed`; keeping raw construction
representable is what lets the checker report the defect rather than making an
unchecked constructor impossible to inspect.
-/
structure BlockContract (State : Type u) where
  requires : State → Prop
  exits : List (ExitContract State)

namespace BlockContract

variable {State : Type u}

/-- The exit identities in declaration order. -/
def exitTags (contract : BlockContract State) : List ExitTag :=
  contract.exits.map ExitContract.tag

/-- Whether a contract declares an exit identity. -/
def declaresExit (contract : BlockContract State) (tag : ExitTag) : Bool :=
  contract.exitTags.contains tag

/-- A contract is structurally well formed exactly when exit identities are
unique.  An empty family is permitted for a genuinely non-returning block. -/
def wellFormed (contract : BlockContract State) : Bool :=
  decide contract.exitTags.Nodup

/-- Proposition consumed by certificate-bearing code.  It is definitionally
the result of the small executable structural checker. -/
def WellFormed (contract : BlockContract State) : Prop :=
  contract.wellFormed = true

instance (contract : BlockContract State) : Decidable contract.WellFormed :=
  inferInstanceAs (Decidable (contract.wellFormed = true))

/-- Public elimination rule for the executable checker.  Consumers need not
unfold the checker to recover exit-identity uniqueness. -/
@[simp] theorem wellFormed_iff (contract : BlockContract State) :
    contract.WellFormed ↔ contract.exitTags.Nodup := by
  simp [WellFormed, wellFormed]

end BlockContract

end Grass.CFG
