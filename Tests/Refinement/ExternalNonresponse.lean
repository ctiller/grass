import Grass.Refinement.ImplementationConformance

/-! A directed-conformance regression: a real, quiet external service loop may
match a fixed upper permanent wait.  This is a small semantic model, not an
instantiation of a native or raw implementation. -/

namespace Grass.Tests.Refinement.ExternalNonresponse

open RelationalSystem

inductive Choice where
  | service
  | reply
deriving DecidableEq

abbrev protocol : WaitProtocol Unit where
  Response := fun _ => Unit
  Allowed := fun _ _ => True
  AllowsPermanentWait := fun _ => True

abbrev system : RelationalSystem Unit where
  State := Bool
  Choice := Choice
  Graph := Unit
  Initial := fun state _ => state = false
  Step := fun _ state choice _ next _ =>
    (state = false ∧ choice = .service ∧ next = false) ∨
    (state = false ∧ choice = .reply ∧ next = true)
  Terminal := fun state _ => state = true
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := Eq
  extendsRefl := fun _ => rfl
  extendsTrans := Eq.trans
  stepExtends := fun _ => rfl

abbrev boundary : system.WaitBoundary protocol where
  Occurrence := Unit
  request := fun _ => ()
  Pending := fun history _ => history.state = false
  External := fun _ choice => choice = .service ∨ choice = .reply
  Reply := fun _ _ choice => choice = .reply
  reply_unique := by intros; rfl
  nonterminal := by
    intro history occurrence pending terminal
    rw [pending] at terminal
    cases terminal
  step_external := by
    intro history occurrence pending choice event next nextGraph step
    rcases step with (⟨_, service, _⟩ | ⟨_, reply, _⟩)
    · exact Or.inl service
    · exact Or.inr reply
  step_pending_or_reply := by
    intro history occurrence pending choice event next nextGraph step
    rcases step with (⟨origin, service, nextEq⟩ | ⟨origin, reply, nextEq⟩)
    · left
      subst next
      simp only [History.append]
    · right
      exact ⟨(), trivial, reply⟩
  reply_allowed := by intros; trivial
  reply_ends := by
    intro history occurrence pending response choice event next nextGraph step reply afterPending
    rcases step with (⟨_, service, _⟩ | ⟨origin, replied, nextEq⟩)
    · cases reply
      cases service
    · cases reply
      subst next
      simp only [History.append] at afterPending
      cases afterPending
  reply_path := by
    intro history occurrence pending response allowed
    refine ⟨history.state, history.graph, .nil, by simp [Path.choices], pending, ?_⟩
    exact ⟨.reply, (), true, (), rfl, Or.inr ⟨pending, rfl, rfl⟩⟩

abbrev model : BehaviorModel Unit where
  Event := Unit
  Observation := Unit
  observationProjection := { project := fun _ => [] }
  Request := Unit
  system := system
  protocol := protocol
  boundary := boundary
  result := fun state _ => if state then some () else none
  terminal_result := by
    intro state graph
    cases state <;> simp
  terminal_no_step := by
    intro state graph terminal choice event next nextGraph step
    rw [terminal] at step
    rcases step with (⟨origin, _, _⟩ | ⟨origin, _, _⟩) <;> cases origin

def initial : model.History := .initial (state := false) (graph := ()) rfl

def quietRun :
    model.system.InfiniteContinuation initial.state initial.graph initial.path.events where
  stateAt := fun _ => false
  graphAt := fun _ => ()
  choiceAt := fun _ => .service
  eventAt := fun _ => ()
  stateZero := rfl
  graphZero := rfl
  step := by intro index; exact Or.inl ⟨rfl, rfl, rfl⟩
  consistent := trivial

def permanent : PermanentWait model.boundary initial := ⟨(), rfl, trivial⟩

def finite : Grass.ImplementationConformance.Finite (lower := model) (upper := model) id where
  Rel := fun _ _ => True
  initialForth := by
    intro history empty
    exact ⟨initial, rfl, trivial⟩
  extendForth := by
    intro left right related next extension
    exact ⟨right, History.Extension.refl _, trivial⟩
  observations := by intros; rfl
  cutForth := by
    intro left right related count
    exact ⟨0, trivial⟩
  cutBack := by
    intro left right related count
    exact ⟨0, trivial⟩

theorem waitMatch : Grass.ImplementationConformance.WaitMatch finite initial initial
    (⟨(), rfl, trivial⟩) permanent where
  related := trivial
  replyForth := by
    intro answer allowed extension
    exact Or.inl ⟨answer, trivial, extension, trivial⟩

def evidence : Grass.ImplementationConformance.ExternalNonresponse finite initial initial
    quietRun permanent where
  cut := 0
  leftWait := ⟨(), rfl, trivial⟩
  matched := waitMatch
  pending := by intro index; rfl
  external := by intro index; exact Or.inl rfl
  unanswered := by intro index response replied; cases replied
  related := by intro index; trivial

/-- The new directed constructor matches a concrete lower infinite execution
to the same upper permanent wait. -/
theorem directedMatch : Grass.ImplementationConformance.CompleteMatch finite
    (.infinite initial quietRun) (.waiting initial permanent) :=
  .externalNonresponse initial initial quietRun permanent evidence

/-- A suffix choice outside external agency rules out this evidence. -/
theorem no_evidence_with_nonexternal {index : Nat}
    (denied : ¬ model.boundary.External evidence.leftWait.occurrence
      (quietRun.choiceAt (evidence.cut + index))) : False :=
  denied (evidence.external index)

/-- A completed reply on a suffix also rules out this evidence. -/
theorem no_evidence_with_reply {index : Nat} {response : Unit}
    (replied : model.boundary.Reply evidence.leftWait.occurrence response
      (quietRun.choiceAt (evidence.cut + index))) : False :=
  evidence.unanswered index response replied

/-- The finite relation fixes every suffix observation to the upper wait. -/
theorem no_evidence_with_observation_disagreement {index : Nat}
    (different : (model.observe (initial.append (quietRun.prefixPath
      (evidence.cut + index)))).map id ≠ model.observe initial) : False :=
  different (Grass.ImplementationConformance.ExternalNonresponse.observations evidence index)

/-- Strict matching still has an actual upper infinite continuation in its
infinite constructor; the directed case above is separate. -/
theorem strict_infinite_has_upper_run {left : model.History}
    {leftRun : model.system.InfiniteContinuation left.state left.graph left.path.events}
    {complete : model.Complete}
    (matched : BehaviorMatching.CompleteMatch finite.Rel
      (Grass.ImplementationConformance.WaitMatch finite)
      (.infinite left leftRun) complete) :
    ∃ right rightRun, complete = .infinite right rightRun := by
  cases matched with
  | infinite left right leftRun rightRun alignment => exact ⟨right, rightRun, rfl⟩

/-- Making each service event observable forbids the same lower loop from
matching the fixed, empty-observation upper wait. -/
abbrev observedModel : BehaviorModel Unit where
  Event := Unit
  Observation := Unit
  observationProjection := .identity Unit
  Request := Unit
  system := system
  protocol := protocol
  boundary := boundary
  result := fun state _ => if state then some () else none
  terminal_result := by
    intro state graph
    cases state <;> simp
  terminal_no_step := by
    intro state graph terminal choice event next nextGraph step
    rw [terminal] at step
    rcases step with (⟨origin, _, _⟩ | ⟨origin, _, _⟩) <;> cases origin

def observedInitial : observedModel.History := .initial (state := false) (graph := ()) rfl

def observedPermanent : PermanentWait observedModel.boundary observedInitial := ⟨(), rfl, trivial⟩

private def observedRelation : HistoryRelation system system
    (fun history => (observedModel.observe history).map id) observedModel.observe where
  Rel := Eq
  initialForth history empty := ⟨history, empty, rfl⟩
  initialBack history empty := ⟨history, empty, rfl⟩
  extendForth := by intros left right equal next extension; subst right; exact ⟨next, extension, rfl⟩
  extendBack := by intros left right equal next extension; subst right; exact ⟨next, extension, rfl⟩
  observations := by intro left right equal; subst right; simp
  cutForth := by intros left right equal count; subst right; exact ⟨count, rfl⟩
  cutBack := by intros left right equal count; subst right; exact ⟨count, rfl⟩

def observedFinite : Grass.ImplementationConformance.Finite
    (lower := observedModel) (upper := observedModel) id :=
  .ofExact observedRelation

private def observedQuietRun : observedModel.system.InfiniteContinuation
    observedInitial.state observedInitial.graph observedInitial.path.events where
  stateAt := fun _ => false
  graphAt := fun _ => ()
  choiceAt := fun _ => .service
  eventAt := fun _ => ()
  stateZero := rfl
  graphZero := rfl
  step := by intro index; exact Or.inl ⟨rfl, rfl, rfl⟩
  consistent := trivial

private theorem quiet_prefix_event_count (length : Nat) :
    (observedQuietRun.prefixEvents length).length = length := by
  induction length with
  | zero => rfl
  | succ length ih =>
    change (observedQuietRun.prefixEvents length ++ [()]).length = length + 1
    simp [ih]

private theorem quiet_prefix_observation_count (length : Nat) :
    (observedModel.observe (observedInitial.append (observedQuietRun.prefixPath length))).length = length := by
  change (observedInitial.path.append (observedQuietRun.prefixPath length)).events.length = length
  rw [Path.events_append]
  rw [InfiniteContinuation.prefixPath_events]
  exact quiet_prefix_event_count length

/-- The finite simulation's observation equality exposes the service event at
every suffix cut, so no candidate can hide it behind the fixed upper wait. -/
theorem observed_publication_rules_out_external_nonresponse
    (candidate : Grass.ImplementationConformance.ExternalNonresponse observedFinite
      observedInitial observedInitial observedQuietRun observedPermanent) : False := by
  have equal := Grass.ImplementationConformance.ExternalNonresponse.observations candidate 1
  have lengths := congrArg List.length equal
  have lowerCount := quiet_prefix_observation_count (candidate.cut + 1)
  have upperCount : (observedModel.observe observedInitial).length = 0 := rfl
  simp only [List.length_map] at lengths
  omega

end Grass.Tests.Refinement.ExternalNonresponse
