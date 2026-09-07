import Grass.Construct.Fragment.Registry
import Grass.Construct.Source.Ast

/-!
# Authored constructor-closure checking

Constructor occurrences are discovered structurally, including generated nodes
whose bodies expand to no instructions. An authored AST carries one exact
checked `ConstructorClosure`; every generated identity must resolve inside that
dependent input before the source can advance to later verification phases.
-/

namespace Grass.Construct.Fragment

universe u

/-- One structural generated-constructor occurrence before block attachment. -/
structure ConstructorOccurrence where
  id : FragmentId
  parents : List FragmentId
  childPath : List Nat
deriving Repr, DecidableEq

/-- A structural occurrence paired with its exact generated body. -/
structure ConstructorNode (Instruction : Type u) where
  occurrence : ConstructorOccurrence
  body : Source Instruction
deriving Repr

namespace Source

variable {Instruction : Type u}

private def constructorOccurrencesAux :
    Source Instruction → List FragmentId → List Nat → List ConstructorOccurrence
  | .empty, _, _ => []
  | .literal _, _, _ => []
  | .generated id body, parents, childPath =>
      ⟨id, parents, childPath⟩ ::
        constructorOccurrencesAux body (parents ++ [id]) childPath
  | .append left right, parents, childPath =>
      constructorOccurrencesAux left parents (childPath ++ [0]) ++
        constructorOccurrencesAux right parents (childPath ++ [1])

/-- All generated-constructor occurrences in structural source order. -/
def constructorOccurrences (source : Source Instruction) :
    List ConstructorOccurrence :=
  constructorOccurrencesAux source [] []

private def constructorNodesAux :
    Source Instruction → List FragmentId → List Nat → List (ConstructorNode Instruction)
  | .empty, _, _ => []
  | .literal _, _, _ => []
  | .generated id body, parents, childPath =>
      ⟨⟨id, parents, childPath⟩, body⟩ ::
        constructorNodesAux body (parents ++ [id]) childPath
  | .append left right, parents, childPath =>
      constructorNodesAux left parents (childPath ++ [0]) ++
        constructorNodesAux right parents (childPath ++ [1])

/-- Generated nodes with the exact bodies selected in the authored hierarchy. -/
def constructorNodes (source : Source Instruction) : List (ConstructorNode Instruction) :=
  constructorNodesAux source [] []

@[simp] theorem constructorOccurrences_empty :
    (Source.empty : Source Instruction).constructorOccurrences = [] := rfl

@[simp] theorem constructorOccurrences_literal (instructions : List Instruction) :
    (Source.literal instructions).constructorOccurrences = [] := rfl

@[simp] theorem constructorOccurrences_generated (id : FragmentId)
    (body : Source Instruction) :
    (Source.generated id body).constructorOccurrences =
      ⟨id, [], []⟩ :: constructorOccurrencesAux body [id] [] := rfl

end Source

end Grass.Construct.Fragment

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x y

/-- One generated-constructor occurrence attached to its containing CFG block. -/
structure LocatedConstructor where
  block : BlockId
  occurrence : ConstructorOccurrence
deriving Repr, DecidableEq

/-- One exact generated node attached to its containing CFG block. -/
structure LocatedConstructorNode (Instruction : Type w) where
  block : BlockId
  node : ConstructorNode Instruction
deriving Repr

namespace Ast

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- Exact constructor occurrences derived from every authored block body. -/
def constructorOccurrences (source : Ast State Terminal Instruction Annotation) :
    List LocatedConstructor :=
  source.blocks.flatMap fun block =>
    block.body.constructorOccurrences.map fun occurrence =>
      ⟨block.cfg.id, occurrence⟩

/-- Exact generated nodes derived from every authored block body. -/
def constructorNodes (source : Ast State Terminal Instruction Annotation) :
    List (LocatedConstructorNode Instruction) :=
  source.blocks.flatMap fun block =>
    block.body.constructorNodes.map fun node => ⟨block.cfg.id, node⟩

end Ast

/-- Authored AST paired with its exact finite checked constructor input. -/
structure ConstructorSource (State : Type u) (Terminal : Type v)
    (Instruction : Type w) (Annotation : Type x) (Effect : Type y)
    (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  ast : Ast State Terminal Instruction Annotation
  closure : ConstructorClosure Instruction State Effect semantics effectModel
  checkedClosure : CheckedConstructorClosure closure

namespace ConstructorSource

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Effect : Type y}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}

/-- Constructor identities explicitly available to this authored source. -/
def availableIds
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) : List FragmentId :=
  source.closure.ids

/-- Unresolved constructor occurrences with exact block and structural location. -/
def unresolved
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) : List LocatedConstructor :=
  source.ast.constructorOccurrences.filter fun located =>
    decide (located.occurrence.id ∉ source.availableIds)

/-- Structural CFG closure plus exact constructor-input closure. -/
def WellFormed
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) : Prop :=
  source.ast.WellFormed ∧ source.unresolved = []

/--
Every generated node is the exact body of one typed application selected from
this source's checked constructor input.

This is intentionally proof-bearing rather than inferred from nominal closure:
an available identity alone does not prove that arbitrary bytes or instructions
are the registered generator's expansion.
-/
def Exact
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) : Prop :=
  ∀ located ∈ source.ast.constructorNodes,
    ∃ selected : SelectedConstructor source.closure source.checkedClosure
        located.node.occurrence.id,
      ∃ application : ConstructorApplication selected,
        application.fragment.source = located.node.body

instance
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) : Decidable source.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Executable authored constructor-closure check. -/
def wellFormed
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) : Bool :=
  decide source.WellFormed

@[simp] theorem wellFormed_iff
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) :
    source.wellFormed ↔ source.WellFormed := by
  simp [wellFormed]

end ConstructorSource

/-- Checked authored source with structural and constructor closure evidence. -/
structure CheckedConstructorSource
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) : Type (max u v w x y) where
  valid : source.WellFormed

/-- Authored constructor source with both checked closure and exact applications. -/
structure CertifiedConstructorSource
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) : Type (max u v w x y) where
  checked : CheckedConstructorSource source
  exact : source.Exact

/-- Stage-specific authored constructor-closure rejection. -/
inductive ConstructorSourceError where
  | structural (entry : BlockId) (blocks : List BlockId)
  | unresolved (occurrences : List LocatedConstructor)
deriving Repr, DecidableEq

/-- Check structural CFG closure before exact constructor reachability. -/
def checkConstructorSource
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (source : ConstructorSource State Terminal Instruction Annotation Effect
      semantics effectModel) :
    Except ConstructorSourceError (CheckedConstructorSource source) :=
  if structural : source.ast.WellFormed then
    if closed : source.unresolved = [] then .ok ⟨structural, closed⟩
    else .error (.unresolved source.unresolved)
  else .error (.structural source.ast.entry source.ast.blockIds)

end Grass.Construct.Source
