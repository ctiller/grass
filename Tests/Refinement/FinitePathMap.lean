import Grass.Refinement.FinitePathMap

namespace Grass.Tests.Refinement.FinitePathMap

open Grass.RelationalSystem

def loop (Event : Type) : RelationalSystem Event where
  State := Unit
  Choice := Bool
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

def mapping : PathMap (loop Unit) (loop Nat) where
  mapState := id
  mapGraph := id
  mapInitial := fun _ => trivial
  mapStep := fun {graph state choice _event next nextGraph} _valid => by
    cases graph; cases state; cases next; cases nextGraph
    cases choice with
    | false => exact .nil
    | true => exact ((Path.nil : (loop Nat).Path () () () ()).snoc
        false 7 () () trivial).snoc true 9 () () trivial

def lowerPath : (loop Unit).Path () () () () :=
  (((Path.nil : (loop Unit).Path () () () ()).snoc false () () () trivial).snoc
    true () () () trivial).snoc false () () () trivial

def lowerHistory : (loop Unit).History := ⟨(), (), (), (), trivial, lowerPath⟩

def oneStep : PathMap (loop Unit) (loop Nat) where
  mapState := id
  mapGraph := id
  mapInitial := fun _ => trivial
  mapStep := fun {graph state choice _event next nextGraph} _valid =>
    (Path.nil : (loop Nat).Path state graph state graph).snoc choice 1 next nextGraph trivial

example : (oneStep.mapPath lowerPath).events = [1, 1, 1] := rfl
example : (oneStep.mapPath lowerPath).choices = lowerPath.choices := rfl

def collapse : PathMap (loop Nat) (loop Bool) where
  mapState := id
  mapGraph := id
  mapInitial := fun _ => trivial
  mapStep := fun {graph state choice _event next nextGraph} _valid => by
    cases graph; cases state; cases next; cases nextGraph
    cases choice with
    | false => exact .nil
    | true => exact (Path.nil : (loop Bool).Path () () () ()).snoc true true () () trivial

example : ((mapping.trans collapse).mapPath lowerPath).events = [true] := rfl
example : (mapping.trans collapse).mapHistory lowerHistory =
    collapse.mapHistory (mapping.mapHistory lowerHistory) :=
  mapping.mapHistory_trans collapse lowerHistory

-- All lower events are identical, but the actual choice determines whether
-- this structural mapper emits zero or two upper transitions.
example : lowerPath.events = [(), (), ()] := rfl
example : lowerPath.choices = [false, true, false] := rfl
example : (mapping.mapPath lowerPath).events = [7, 9] := rfl
example : (mapping.mapPath lowerPath).choices = [false, true] := rfl
example : (mapping.mapPath lowerPath).length = 2 := rfl

example : (mapping.mapHistory (lowerHistory.restrict 1)).path.events = [] := rfl
example : (mapping.mapHistory (lowerHistory.restrict 2)).path.events = [7, 9] := rfl
example : (mapping.mapHistory (lowerHistory.restrict 3)).path.events = [7, 9] := rfl

-- Restricting a lower path is not the same as retaining that many upper steps.
example : (mapping.mapHistory (lowerHistory.restrict 1)).path.events ≠
    (mapping.mapHistory lowerHistory).path.events.take 1 := by decide

example (count : Nat) :
    (mapping.mapHistory (lowerHistory.restrict count)).append
        (mapping.mapPath (lowerHistory.path.cut count).after) =
      mapping.mapHistory lowerHistory := mapping.mapHistory_restrict_append _ _

-- The mapper cannot manufacture a terminal proof from its finite path laws.
example : ¬ (loop Nat).Terminal (mapping.mapHistory lowerHistory).state
    (mapping.mapHistory lowerHistory).graph := by intro impossible; exact impossible

end Grass.Tests.Refinement.FinitePathMap
