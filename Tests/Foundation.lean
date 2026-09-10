import Grass.Core.Demand
import Grass.Refinement.BehaviorCorrespondenceLaws
import Grass.Refinement.ImplementationConformance

/-! Independent demand, observation, history, and correspondence laws. -/

namespace Grass.Tests.Foundation

open RelationalSystem

inductive NoDemand

def noDemands : DemandFamily where
  Key := NoDemand
  keys := []
  complete := fun key => nomatch key
  unique := by simp
  identity := fun key => nomatch key
  identityInjective := fun left => nomatch left
  kind := fun key => nomatch key
  statement := fun key => nomatch key

namespace DemandFixture

def prior : RequirementKey := ⟨⟨"foundation-fixture", "prior"⟩⟩

def demands : DemandFamily where
  Key := Bool
  keys := [false, true]
  complete := by intro key; cases key <;> simp
  unique := by simp
  identity
    | false => ⟨⟨"foundation-fixture", "false"⟩⟩
    | true => ⟨⟨"foundation-fixture", "true"⟩⟩
  identityInjective := by intro left right equal; cases left <;> cases right <;> simp_all
  kind := fun _ => .functional
  statement := fun _ => True

def stage : DerivedDemandFamily [prior] where
  demands := demands
  origin := fun _ => .external ⟨"foundation-fixture", "authority"⟩
  fresh := by intro key; cases key <;> simp [prior, demands]

example (key : demands.Key) : demands.identity key ∈ demands.identities :=
  demands.identity_mem_identities key

example : demands.identities.Nodup := demands.identities_nodup

example : prior ∈ stage.allKeys := stage.prior_mem_allKeys (by simp [prior])

example (key : demands.Key) : demands.identity key ∈ stage.allKeys :=
  stage.identity_mem_allKeys key

example : stage.allKeys.Nodup := stage.allKeys_nodup (by simp [prior])

inductive FinalDemand | only

def finalDemands : DemandFamily where
  Key := FinalDemand
  keys := [.only]
  complete := by intro key; cases key; simp
  unique := by simp
  identity := fun _ => ⟨⟨"foundation-fixture", "final"⟩⟩
  identityInjective := by intro left right _; cases left; cases right; rfl
  kind := fun _ => .artifact
  statement := fun _ => True

def finalStage : DerivedDemandFamily stage.allKeys where
  demands := finalDemands
  origin := fun _ => .external ⟨"foundation-fixture", "final-authority"⟩
  fresh := by
    intro key
    cases key
    simp [stage, demands, prior, finalDemands, DerivedDemandFamily.allKeys,
      DemandFamily.identities]

example : finalStage.allKeys.Nodup :=
  finalStage.allKeys_nodup (stage.allKeys_nodup (by simp [prior]))

end DemandFixture

namespace ObservationFixture

def boolToNat : ObservationProjection Bool Nat where
  project := fun events => events.map Bool.toNat

def natToString : ObservationProjection Nat String where
  project := fun events => events.map toString

def stringLengths : ObservationProjection String Nat where
  project := fun events => events.map String.length

example : (ObservationProjection.identity Nat).comp boolToNat = boolToNat := by
  apply ObservationProjection.identity_comp

example : boolToNat.comp (ObservationProjection.identity Bool) = boolToNat := by
  apply ObservationProjection.comp_identity

example (events : List Bool) :
    (natToString.comp boolToNat).project events =
      natToString.project (boolToNat.project events) :=
  ObservationProjection.comp_project natToString boolToNat events

example : (stringLengths.comp natToString).comp boolToNat =
    stringLengths.comp (natToString.comp boolToNat) :=
  ObservationProjection.comp_assoc stringLengths natToString boolToNat

end ObservationFixture

namespace HistoryFixture

abbrev system : RelationalSystem Bool where
  State := Nat
  Choice := Unit
  Graph := Nat
  Initial := fun state graph => state = 0 ∧ graph = 0
  Step := fun before state _ event next after =>
    next = state + 1 ∧ after = before + 1 ∧ event = (state % 2 == 1)
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := Nat.le
  extendsRefl := Nat.le_refl
  extendsTrans := Nat.le_trans
  stepExtends := fun transition => transition.2.1 ▸ Nat.le_succ _

def initial : system.History := .initial (state := 0) (graph := 0) ⟨rfl, rfl⟩

def first : system.Path 0 0 1 1 :=
  Path.snoc (system := system) .nil () false (1 : Nat) (1 : Nat)
    ⟨rfl, rfl, rfl⟩

def second : system.Path 1 1 2 2 :=
  Path.snoc (system := system) .nil () true (2 : Nat) (2 : Nat)
    ⟨rfl, rfl, rfl⟩

example : (initial.append first).path.events = [false] := rfl

example : (first.append second).events = [false, true] := rfl

example : first.append (.nil) = first := Path.append_nil first

def indexedContinuation : system.InfiniteContinuation 0 0 [] where
  stateAt := fun index => index
  graphAt := fun index => index
  choiceAt := fun _ => ()
  eventAt := fun index => index % 2 == 1
  stateZero := rfl
  graphZero := rfl
  step := fun _ => ⟨rfl, rfl, rfl⟩
  consistent := trivial

example : indexedContinuation.prefixEvents 3 = [false, true, false] := rfl

example : (indexedContinuation.prefixPath 3).events = [false, true, false] := by
  rw [indexedContinuation.prefixPath_events]
  rfl

example : system.Steps 0 0 [false, true, false] 3 3 := by
  have steps := indexedContinuation.prefixSteps 3
  change system.Steps 0 0 (indexedContinuation.prefixEvents 3)
    (indexedContinuation.stateAt 3) (indexedContinuation.graphAt 3) at steps
  exact steps

example : system.Extends 0 (indexedContinuation.graphAt 3) :=
  indexedContinuation.graphExtendsAt 3

abbrev protocol : WaitProtocol Empty where
  Response := fun request => nomatch request
  Allowed := fun request => nomatch request
  AllowsPermanentWait := fun request => nomatch request

abbrev boundary : system.WaitBoundary protocol where
  Occurrence := Empty
  request := fun occurrence => nomatch occurrence
  Pending := fun _ occurrence => nomatch occurrence
  External := fun occurrence => nomatch occurrence
  Reply := fun occurrence => nomatch occurrence
  reply_unique := by intro occurrence; exact nomatch occurrence
  nonterminal := by intro history occurrence; exact nomatch occurrence
  step_external := by intro history occurrence; exact nomatch occurrence
  step_pending_or_reply := by intro history occurrence; exact nomatch occurrence
  reply_allowed := by intro history occurrence; exact nomatch occurrence
  reply_ends := by intro history occurrence; exact nomatch occurrence
  reply_path := by intro history occurrence; exact nomatch occurrence

abbrev model : BehaviorModel Unit where
  Event := Bool
  Observation := Bool
  observationProjection := .identity Bool
  Request := Empty
  system := system
  protocol := protocol
  boundary := boundary
  result := fun _ _ => none
  terminal_result := by simp [system]
  terminal_no_step := by intro _ _ terminal; exact False.elim terminal

example : BehaviorCorrespondence model model id (WaitTranslation.refl model) :=
  BehaviorCorrespondence.refl model

example : ImplementationConformance model model id :=
  (BehaviorCorrespondence.refl model).toImplementationConformance

end HistoryFixture

namespace PriorSensitiveInfiniteFixture

abbrev system : RelationalSystem Bool where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => False
  InfiniteConsistent := fun priorEvents _ _ _ eventAt =>
    priorEvents = [true] ∧ eventAt 0 = false
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

def initial : system.History := .initial (state := ()) (graph := ()) trivial

def first : system.Path () () () () :=
  Path.snoc (system := system) .nil () true () () trivial

def retained : system.History := initial.append first

def continuation : system.InfiniteContinuation retained.state retained.graph
    retained.path.events where
  stateAt := fun _ => ()
  graphAt := fun _ => ()
  choiceAt := fun _ => ()
  eventAt := fun _ => false
  stateZero := rfl
  graphZero := rfl
  step := fun _ => trivial
  consistent := ⟨rfl, rfl⟩

example : retained.path.events = [true] := rfl

example : continuation.eventAt 0 = false := rfl

example : system.InfiniteConsistent retained.path.events continuation.stateAt
    continuation.graphAt continuation.choiceAt continuation.eventAt := continuation.consistent

example : (continuation.prefixPath 1).events = [false] := by
  rw [continuation.prefixPath_events]
  rfl

end PriorSensitiveInfiniteFixture

end Grass.Tests.Foundation
