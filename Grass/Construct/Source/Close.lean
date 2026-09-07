import Grass.CFG.Compose
import Grass.Construct.Source.Discover

/-!
# Hierarchical authored source closure

`Closure` combines exact join and loop selections with a finite available-item
set.  `Closure.unresolvedLocated` reports every missing demand at its containing
block and `SourceOrigin`; it is derived from `Ast.discoverItems` rather than a
separately authored diagnostic table.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x y

/-- Explicit closure selections for one exact authored source and projection. -/
structure Closure {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Item : Type y}
    (source : Ast State Terminal Instruction Annotation)
    (model : ManifestModel Instruction Item) where
  joins : JoinSelection source.toGraph
  loops : LoopSelection source.toGraph
  available : List Item

namespace Closure

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x} {Item : Type y}
  {source : Ast State Terminal Instruction Annotation}
  {model : ManifestModel Instruction Item}
  [DecidableEq Item]

/-- Missing projected occurrences, retaining exact authored locations. -/
def unresolvedLocated (closure : Closure source model) : List (LocatedItem Item) :=
  (source.discoverItems model).filter fun located =>
    decide (located.item ∉ closure.available)

/-- Executable closure check over the source's exact structural projections. -/
def wellFormed (closure : Closure source model) : Bool :=
  closure.joins.wellFormed &&
  closure.loops.wellFormed &&
  decide closure.available.Nodup &&
  closure.unresolvedLocated.isEmpty

/-- Certificate-facing statement for `Closure.wellFormed`. -/
def WellFormed (closure : Closure source model) : Prop := closure.wellFormed = true

instance (closure : Closure source model) : Decidable closure.WellFormed :=
  inferInstanceAs (Decidable (closure.wellFormed = true))

/-- Public decomposition of authored-source closure. -/
@[simp] theorem wellFormed_iff (closure : Closure source model) :
    closure.WellFormed ↔
      ((closure.joins.WellFormed ∧ closure.loops.WellFormed) ∧
        closure.available.Nodup) ∧ closure.unresolvedLocated = [] := by
  simp [WellFormed, wellFormed, JoinSelection.WellFormed,
    LoopSelection.WellFormed]

/-- A closed source has no missing located demand. -/
theorem unresolvedLocated_eq_nil (closure : Closure source model)
    (closed : closure.WellFormed) : closure.unresolvedLocated = [] :=
  (wellFormed_iff closure).mp closed |>.2

end Closure

end Grass.Construct.Source
