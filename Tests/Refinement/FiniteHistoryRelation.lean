import Grass.Refinement.FiniteHistoryRelation

namespace Grass.Tests.Refinement.FiniteHistoryRelation

open Grass RelationalSystem

def lower : RelationalSystem Bool where
  State := Nat
  Choice := Bool
  Graph := Nat
  Initial state graph := state = 0 ∧ graph = 0
  Step graph state _choice _event next nextGraph :=
    next = state + 1 ∧ nextGraph = graph + 1
  Terminal _ _ := False
  InfiniteConsistent _ _ _ _ _ := True
  Extends before after := before ≤ after
  extendsRefl _ := Nat.le_refl _
  extendsTrans := Nat.le_trans
  stepExtends valid := by omega

def upper : RelationalSystem Nat where
  State := Nat
  Choice := Nat
  Graph := Nat
  Initial state graph := state = 0 ∧ graph = 0
  Step graph state _choice _event next nextGraph :=
    next = state + 1 ∧ nextGraph = graph + 1
  Terminal _ _ := False
  InfiniteConsistent _ _ _ _ _ := True
  Extends before after := before ≤ after
  extendsRefl _ := Nat.le_refl _
  extendsTrans := Nat.le_trans
  stepExtends valid := by omega

def lowerInitial : lower.History := History.initial ⟨rfl, rfl⟩
def upperInitial : upper.History := History.initial ⟨rfl, rfl⟩

def lowerStep (choice event : Bool) (state graph : Nat) :
    lower.Path state graph (state + 1) (graph + 1) :=
  .snoc .nil choice event _ _ ⟨rfl, rfl⟩

def upperStep (choice event state graph : Nat) :
    upper.Path state graph (state + 1) (graph + 1) :=
  .snoc .nil choice event _ _ ⟨rfl, rfl⟩

def lowerTrue : lower.History := lowerInitial.append (lowerStep true false 0 0)
def lowerFalse : lower.History := lowerInitial.append (lowerStep false false 0 0)
def lowerTwo : lower.History :=
  lowerTrue.append (lowerStep false true 1 1)

def upperOne : upper.History := upperInitial.append (upperStep 7 10 0 0)
def upperTwo : upper.History := upperOne.append (upperStep 8 20 1 1)

/-- Distinct choices remain distinguishable even when the event traces agree. -/
example : lowerTrue.path.events = lowerFalse.path.events := rfl
example : lowerTrue.path.choices ≠ lowerFalse.path.choices := by
  intro equal
  have heads := congrArg List.head? equal
  change some true = some false at heads
  have impossible : true = false := Option.some.inj heads
  exact Bool.noConfusion impossible

/-- These are exact history extensions, not merely equal endpoints. -/
example : History.Extension lowerInitial lowerTrue :=
  ⟨_, _, lowerStep true false 0 0, rfl⟩
example : History.Extension lowerTrue lowerTwo :=
  ⟨_, _, lowerStep false true 1 1, rfl⟩

def forgetful : HistoryRelation lower upper (fun _ => ()) (fun _ => ()) where
  Rel _ _ := True
  initialForth _ _ := ⟨upperInitial, rfl, trivial⟩
  initialBack _ _ := ⟨lowerInitial, rfl, trivial⟩
  extendForth := by
    intro left right related next extension
    exact ⟨right, History.Extension.refl right, trivial⟩
  extendBack := by
    intro left right related next extension
    exact ⟨left, History.Extension.refl left, trivial⟩
  observations _ := rfl
  cutForth _ _ := ⟨0, trivial⟩
  cutBack _ _ := ⟨0, trivial⟩

/-- The finite relation admits zero/one/many histories and aligned cuts whose
counts differ; it does not impose a one-step correspondence. -/
example : forgetful.Rel lowerInitial upperInitial := by change True; trivial
example : forgetful.Rel lowerTrue upperOne := by change True; trivial
example : forgetful.Rel lowerTrue upperTwo := by change True; trivial
example : ∃ upperCount, forgetful.Rel (lowerTwo.restrict 1)
    (upperTwo.restrict upperCount) := by
  apply forgetful.cutForth (left := lowerTwo) (right := upperTwo)
  trivial

/-- Restriction retains an exact suffix that reconstructs the choice-bearing history. -/
example : (lowerTwo.restrict 1).append (lowerTwo.path.cut 1).after = lowerTwo :=
  lowerTwo.restrict_append 1

def visibleLower (history : lower.History) : Bool := history.path.choices.head?.getD true
def visibleUpper (_history : upper.History) : Bool := true

/-- A relation preserving the chosen visibility cannot invent backward coverage
for the discarded `false` branch, despite its event trace matching `lowerTrue`. -/
theorem discarded_visible_branch_refused
    (relation : HistoryRelation lower upper visibleLower visibleUpper) :
    ¬ relation.Rel lowerFalse upperOne := by
  intro related
  have observed := relation.observations related
  change false = true at observed
  have impossible : false = true := observed
  exact Bool.noConfusion impossible

/-- Initial coverage and extension matching force the discarded branch to be
checked, even if a proposed relation refuses to relate that branch directly. -/
theorem discarded_branch_prevents_correspondence :
    ¬ Nonempty (HistoryRelation lower upper visibleLower visibleUpper) := by
  rintro ⟨relation⟩
  obtain ⟨initial, _, related⟩ := relation.initialForth lowerInitial rfl
  have extension : History.Extension lowerInitial lowerFalse :=
    ⟨_, _, lowerStep false false 0 0, rfl⟩
  obtain ⟨next, _, nextRelated⟩ := relation.extendForth related extension
  have observed := relation.observations nextRelated
  change false = true at observed
  exact Bool.noConfusion observed

end Grass.Tests.Refinement.FiniteHistoryRelation
