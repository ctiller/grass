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
  | empty
  | literal (instructions : List Instruction)
  | generated (id : FragmentId) (body : Source Instruction)
  | append (left right : Source Instruction)
deriving Repr

/-- Structural origin of one expanded instruction.  Generator identities are
ordered outermost to innermost; child indices locate sequence branches; the
literal index locates the instruction within its leaf. -/
structure SourceOrigin where
  generators : List FragmentId
  childPath : List Nat
  literalIndex : Nat
deriving Repr, DecidableEq

/-- One instruction paired with its exact structural origin. -/
structure LocatedInstruction (Instruction : Type u) where
  origin : SourceOrigin
  instruction : Instruction
deriving Repr, DecidableEq

namespace Source

variable {Instruction : Type u}

/-- Build an n-ary sequence over the binary hierarchical core. -/
def sequence (children : List (Source Instruction)) : Source Instruction :=
  children.foldr Source.append .empty

private def expandRaw : Source Instruction → List Instruction
  | .empty => []
  | .literal instructions => instructions
  | .generated _ body => body.expandRaw
  | .append left right => left.expandRaw ++ right.expandRaw

private def locateLiterals (generators : List FragmentId) (childPath : List Nat) :
    Nat → List Instruction → List (LocatedInstruction Instruction)
  | _, [] => []
  | index, instruction :: rest =>
      ⟨⟨generators, childPath, index⟩, instruction⟩ ::
        locateLiterals generators childPath (index + 1) rest

private theorem map_locateLiterals (generators : List FragmentId)
    (childPath : List Nat) (index : Nat) (instructions : List Instruction) :
    (locateLiterals generators childPath index instructions).map
      LocatedInstruction.instruction = instructions := by
  induction instructions generalizing index with
  | nil => rfl
  | cons instruction rest ih =>
      simp [locateLiterals, ih]

private def expandLocatedAux : Source Instruction → List FragmentId → List Nat →
    List (LocatedInstruction Instruction)
  | .empty, _, _ => []
  | .literal instructions, generators, childPath =>
      locateLiterals generators childPath 0 instructions
  | .generated id body, generators, childPath =>
      expandLocatedAux body (generators ++ [id]) childPath
  | .append left right, generators, childPath =>
      expandLocatedAux left generators (childPath ++ [0]) ++
        expandLocatedAux right generators (childPath ++ [1])

/-- Exact expansion paired one-for-one with structural source origins. -/
def expandLocated (source : Source Instruction) : List (LocatedInstruction Instruction) :=
  expandLocatedAux source [] []

/-- Select the structural source location at one flat expansion index. -/
def locatedInstructionAt? (source : Source Instruction) (index : Nat) :
    Option (LocatedInstruction Instruction) :=
  source.expandLocated[index]?

/-- Exact flat instruction expansion in structural source order. -/
def expand (source : Source Instruction) : List Instruction :=
  source.expandRaw

private theorem expandRaw_eq_map_expandLocatedAux
    (source : Source Instruction) (generators : List FragmentId)
    (childPath : List Nat) :
    source.expandRaw =
      (expandLocatedAux source generators childPath).map
        LocatedInstruction.instruction := by
  induction source generalizing generators childPath with
  | empty => rfl
  | literal instructions =>
      simpa [expandRaw, expandLocatedAux] using
        (map_locateLiterals generators childPath 0 instructions).symm
  | generated id body ih =>
      simp [expandRaw, expandLocatedAux]
      exact ih (generators ++ [id]) childPath
  | append left right leftIh rightIh =>
      simp only [expandRaw, expandLocatedAux, List.map_append]
      rw [← leftIh generators (childPath ++ [0]),
        ← rightIh generators (childPath ++ [1])]

/-- Flat expansion is exactly the instruction projection of the total located
expansion. -/
theorem expand_eq_map_located (source : Source Instruction) :
    source.expand = source.expandLocated.map LocatedInstruction.instruction := by
  exact expandRaw_eq_map_expandLocatedAux source [] []

/-- `Source.expandLocated_length` proves that the source map has exactly one
entry for every expanded instruction. -/
theorem expandLocated_length (source : Source Instruction) :
    source.expandLocated.length = source.expand.length := by
  rw [source.expand_eq_map_located, List.length_map]

/-- `Source.instruction_of_locatedInstructionAt?` proves that indexed source
lookup projects to the instruction at the same flat expansion index. -/
theorem instruction_of_locatedInstructionAt? (source : Source Instruction)
    (index : Nat) :
    (source.locatedInstructionAt? index).map LocatedInstruction.instruction =
      source.expand[index]? := by
  rw [source.expand_eq_map_located]
  simp [locatedInstructionAt?]

/-- Number of literal leaves in the hierarchy. -/
def leafCount : Source Instruction → Nat
  | .empty => 0
  | .literal _ => 1
  | .generated _ body => body.leafCount
  | .append left right => left.leafCount + right.leafCount

/-- Number of instructions in the exact expansion. -/
def instructionCount (source : Source Instruction) : Nat := source.expand.length

@[simp] theorem locatedInstructionAt?_isSome_iff
    (source : Source Instruction) (index : Nat) :
    (source.locatedInstructionAt? index).isSome = true ↔
      index < source.instructionCount := by
  simp [locatedInstructionAt?, instructionCount, source.expandLocated_length]

@[simp] theorem expand_literal (instructions : List Instruction) :
    (Source.literal instructions).expand = instructions := by
  simp [expand, expandRaw]

@[simp] theorem expand_generated (id : FragmentId) (body : Source Instruction) :
    (Source.generated id body).expand = body.expand := by
  simp [expand, expandRaw]

@[simp] theorem expand_sequence (children : List (Source Instruction)) :
    (Source.sequence children).expand = children.flatMap expand := by
  induction children with
  | nil => simp [sequence, expand, expandRaw]
  | cons child rest ih =>
      change child.expandRaw ++ (Source.sequence rest).expandRaw =
        child.expandRaw ++ rest.flatMap expand
      have ihRaw : (Source.sequence rest).expandRaw = rest.flatMap expand := by
        simpa [expand] using ih
      rw [ihRaw]

@[simp] theorem leafCount_literal (instructions : List Instruction) :
    (Source.literal instructions).leafCount = 1 := by simp [leafCount]

@[simp] theorem leafCount_generated (id : FragmentId)
    (body : Source Instruction) :
    (Source.generated id body).leafCount = body.leafCount := by simp [leafCount]

@[simp] theorem leafCount_sequence (children : List (Source Instruction)) :
    (Source.sequence children).leafCount = (children.map leafCount).sum := by
  induction children with
  | nil => simp [sequence, leafCount]
  | cons child rest ih =>
      change child.leafCount + (sequence rest).leafCount =
        child.leafCount + (rest.map leafCount).sum
      rw [ih]

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
