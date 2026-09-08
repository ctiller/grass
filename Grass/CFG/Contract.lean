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

/-- Find one exit contract by stable identity. -/
def findExit? (contract : BlockContract State) (tag : ExitTag) :
    Option (ExitContract State) :=
  contract.exits.find? (fun exit => exit.tag == tag)

/-- Whether a contract declares an exit identity. -/
def declaresExit (contract : BlockContract State) (tag : ExitTag) : Bool :=
  contract.exitTags.contains tag

/-- A successful exit lookup returns a declared member with the requested
identity. -/
theorem findExit?_sound
    (contract : BlockContract State) (tag : ExitTag)
    (exit : ExitContract State)
    (hfind : contract.findExit? tag = some exit) :
    exit ∈ contract.exits ∧ exit.tag = tag := by
  constructor
  · exact List.mem_of_find?_eq_some (by
      simpa [findExit?] using hfind)
  · have matched : exit.tag == tag := List.find?_some
      (p := fun candidate : ExitContract State => candidate.tag == tag) (by
        simpa [findExit?] using hfind)
    exact LawfulBEq.eq_of_beq matched

/-- Exit lookup succeeds exactly when the contract declares the identity. -/
theorem findExit?_isSome_iff_declaresExit
    (contract : BlockContract State) (tag : ExitTag) :
    (contract.findExit? tag).isSome = true ↔
      contract.declaresExit tag = true := by
  simp [findExit?, declaresExit, exitTags]

/-- Every declared exit identity has a concrete exit-contract lookup result. -/
theorem exitForTag
    (contract : BlockContract State) (tag : ExitTag)
    (declared : contract.declaresExit tag = true) :
    ∃ exit, contract.findExit? tag = some exit := by
  apply Option.isSome_iff_exists.mp
  exact (contract.findExit?_isSome_iff_declaresExit tag).2 declared

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

private theorem exit_eq_of_mem_of_mem_of_tags_nodup
    {exits : List (ExitContract State)} {left right : ExitContract State}
    (unique : (exits.map ExitContract.tag).Nodup)
    (leftMem : left ∈ exits) (rightMem : right ∈ exits)
    (sameTag : left.tag = right.tag) : left = right := by
  induction exits with
  | nil => simp at leftMem
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at unique
      rw [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          apply unique.1
          rw [sameTag]
          exact List.mem_map.mpr ⟨right, rightMem, rfl⟩
      · rcases rightMem with rfl | rightMem
        · exfalso
          apply unique.1
          rw [← sameTag]
          exact List.mem_map.mpr ⟨left, leftMem, rfl⟩
        · exact ih unique.2 leftMem rightMem

/-- `BlockContract.exit_eq_of_mem_of_mem_of_tag_eq` proves that two declared
exits of a well-formed contract with the same tag are the same exit. -/
theorem exit_eq_of_mem_of_mem_of_tag_eq
    (contract : BlockContract State) (left right : ExitContract State)
    (closed : contract.WellFormed)
    (leftMem : left ∈ contract.exits) (rightMem : right ∈ contract.exits)
    (sameTag : left.tag = right.tag) : left = right := by
  apply exit_eq_of_mem_of_mem_of_tags_nodup
  · exact (wellFormed_iff contract).mp closed
  · exact leftMem
  · exact rightMem
  · exact sameTag

/-- Under `BlockContract.WellFormed`, lookup of a declared exit is canonical:
`BlockContract.findExit?_eq_some_of_mem` returns that exact member. -/
theorem findExit?_eq_some_of_mem
    (contract : BlockContract State) (tag : ExitTag)
    (exit : ExitContract State) (closed : contract.WellFormed)
    (member : exit ∈ contract.exits) (hasTag : exit.tag = tag) :
    contract.findExit? tag = some exit := by
  have declared : contract.declaresExit tag = true := by
    simp [declaresExit, exitTags]
    exact ⟨exit, member, hasTag⟩
  obtain ⟨found, foundLookup⟩ := contract.exitForTag tag declared
  have foundFacts := contract.findExit?_sound tag found foundLookup
  have foundEq : found = exit :=
    contract.exit_eq_of_mem_of_mem_of_tag_eq found exit closed
      foundFacts.1 member (foundFacts.2.trans hasTag.symm)
  simpa [foundEq] using foundLookup

end BlockContract

end Grass.CFG
