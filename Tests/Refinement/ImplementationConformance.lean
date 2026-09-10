import Grass.Refinement.ImplementationConformance

/-!
# Directed implementation conformance fixture

The lower model completes only successfully.  The upper model also has an
actual error completion, which this directed relation deliberately does not
cover backwards.  The fixture uses initialized histories and complete-history
matching rather than a bare relation witness.
-/

namespace Grass.Tests.Refinement.ImplementationConformance

open RelationalSystem

abbrev terminalSystem : RelationalSystem Unit where
  State := Bool
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => False
  Terminal := fun _ _ => True
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := by
    intro a b c ab bc
    trivial
  stepExtends := by
    intro before state choice event next after step
    exact False.elim step

abbrev noRequests : WaitProtocol.{0, 0} Empty where
  Response := fun request => nomatch request
  Allowed := fun request => nomatch request
  AllowsPermanentWait := fun request => nomatch request

abbrev noWaitBoundary : terminalSystem.WaitBoundary noRequests where
  Occurrence := Empty
  request := fun occurrence => nomatch occurrence
  Pending := fun _ occurrence => nomatch occurrence
  Reply := fun occurrence => nomatch occurrence
  reply_unique := by
    intro occurrence
    exact nomatch occurrence
  nonterminal := by
    intro history occurrence
    exact nomatch occurrence
  step_reply := by
    intro history occurrence
    exact nomatch occurrence
  reply_step := by
    intro history occurrence
    exact nomatch occurrence

/-- `true` denotes success and `false` denotes error. -/
abbrev successOnly : BehaviorModel Bool where
  Event := Unit
  Observation := Unit
  observationProjection := { project := fun _ => [] }
  Request := Empty
  system := terminalSystem
  protocol := noRequests
  boundary := noWaitBoundary
  result := fun _ _ => some true
  terminal_result := by simp [terminalSystem]
  terminal_no_step := by
    intro state graph terminal choice event next nextGraph step
    exact False.elim step

/-- This upper model has both a successful and an error terminal initial history. -/
abbrev successOrError : BehaviorModel Bool where
  Event := Unit
  Observation := Unit
  observationProjection := { project := fun _ => [] }
  Request := Empty
  system := terminalSystem
  protocol := noRequests
  boundary := noWaitBoundary
  result := fun state _ => some state
  terminal_result := by simp [terminalSystem]
  terminal_no_step := by
    intro state graph terminal choice event next nextGraph step
    exact False.elim step

def successOnlyInitial : successOnly.History :=
  .initial (state := true) (graph := ()) trivial

def successOrErrorInitial : successOrError.History :=
  .initial (state := true) (graph := ()) trivial

def successOrErrorErrorInitial : successOrError.History :=
  .initial (state := false) (graph := ()) trivial

def successTranslation : DirectedWaitTranslation successOnly successOrError where
  request := fun request => nomatch request
  response := fun request => nomatch request
  allowed := by
    intro request
    exact nomatch request
  permanent := by
    intro request
    exact nomatch request

def successFinite : Grass.ImplementationConformance.Finite
    (lower := successOnly) (upper := successOrError) id where
  Rel := fun _ right => right = successOrErrorInitial
  initialForth := by
    intro history empty
    exact ⟨successOrErrorInitial, rfl, rfl⟩
  extendForth := by
    intro left right related next extension
    subst right
    exact ⟨successOrErrorInitial, History.Extension.refl _, rfl⟩
  observations := by
    intro left right related
    rfl
  cutForth := by
    intro left right related count
    subst right
    exact ⟨0, rfl⟩
  cutBack := by
    intro left right related count
    subst right
    exact ⟨0, rfl⟩

theorem no_infinite_success_only {history : successOnly.History}
    (run : successOnly.system.InfiniteContinuation history.state history.graph history.path.events) : False := by
  exact run.step 0

theorem no_wait_success_only {history : successOnly.History}
    (waiting : PermanentWait successOnly.boundary history) : False := by
  exact waiting.not_terminal trivial

def successConformance : Grass.ImplementationConformance successOnly successOrError id
    successTranslation where
  finite := successFinite
  completeForth := by
    intro left right related complete starts
    subst right
    cases complete with
    | terminal history finished =>
      refine ⟨.terminal successOrErrorInitial trivial, History.Extension.refl _, ?_⟩
      apply BehaviorMatching.CompleteMatch.terminal
      · exact rfl
      · rfl
    | infinite history continuation =>
      exact False.elim (no_infinite_success_only continuation)
    | waiting history waiting =>
      exact False.elim (no_wait_success_only waiting)

/-- A lower terminal completion can only be matched by an upper terminal
completion with the same outcome. -/
theorem terminal_counterpart_required {Outcome : Type} {lower upper : BehaviorModel Outcome}
    {observe : lower.Observation → upper.Observation}
    {waits : DirectedWaitTranslation lower upper}
    (conformance : Grass.ImplementationConformance lower upper observe waits)
    {left : lower.History} {right : upper.History} {lowerHistory : lower.History}
    (related : conformance.finite.Rel left right)
    (finished : lower.system.Terminal lowerHistory.state lowerHistory.graph)
    (starts : BehaviorModel.Complete.StartsAfter left (.terminal lowerHistory finished)) :
    ∃ upperHistory : upper.History,
      ∃ upperFinished : upper.system.Terminal upperHistory.state upperHistory.graph,
        BehaviorModel.Complete.StartsAfter right (.terminal upperHistory upperFinished) ∧
        lower.result lowerHistory.state lowerHistory.graph = upper.result upperHistory.state upperHistory.graph := by
  obtain ⟨other, otherStarts, matched⟩ := conformance.completeForth related
    (.terminal lowerHistory finished) starts
  cases matched with
  | terminal leftMatched rightMatched leftDone rightDone relatedMatched outcomes =>
    exact ⟨rightMatched, rightDone, otherStarts, outcomes⟩

/-- A divergent lower completion cannot be erased: its counterpart has an
actual upper infinite continuation. -/
theorem infinite_counterpart_required {Outcome : Type} {lower upper : BehaviorModel Outcome}
    {observe : lower.Observation → upper.Observation}
    {waits : DirectedWaitTranslation lower upper}
    (conformance : Grass.ImplementationConformance lower upper observe waits)
    {left : lower.History} {right : upper.History} {lowerHistory : lower.History}
    (related : conformance.finite.Rel left right)
    (run : lower.system.InfiniteContinuation lowerHistory.state lowerHistory.graph lowerHistory.path.events)
    (starts : BehaviorModel.Complete.StartsAfter left (.infinite lowerHistory run)) :
    ∃ upperHistory run,
      BehaviorModel.Complete.StartsAfter right (.infinite upperHistory run) := by
  obtain ⟨other, otherStarts, matched⟩ := conformance.completeForth related
    (.infinite lowerHistory run) starts
  cases matched with
  | infinite leftMatched rightMatched leftRun rightRun alignment =>
    exact ⟨rightMatched, rightRun, otherStarts⟩

/-- A permitted lower permanent wait cannot be erased: its counterpart retains
an actual upper permanent-wait witness. -/
theorem waiting_counterpart_required {Outcome : Type} {lower upper : BehaviorModel Outcome}
    {observe : lower.Observation → upper.Observation}
    {waits : DirectedWaitTranslation lower upper}
    (conformance : Grass.ImplementationConformance lower upper observe waits)
    {left : lower.History} {right : upper.History} {lowerHistory : lower.History}
    (related : conformance.finite.Rel left right)
    (waiting : PermanentWait lower.boundary lowerHistory)
    (starts : BehaviorModel.Complete.StartsAfter left (.waiting lowerHistory waiting)) :
    ∃ upperHistory upperWaiting,
      BehaviorModel.Complete.StartsAfter right (.waiting upperHistory upperWaiting) := by
  obtain ⟨other, otherStarts, matched⟩ := conformance.completeForth related
    (.waiting lowerHistory waiting) starts
  cases matched with
  | waiting leftMatched rightMatched leftWait rightWait matchedWait =>
    exact ⟨rightMatched, rightWait, otherStarts⟩

/-- A lower actual error cannot conform to a success-only upper model: terminal
matching requires equality of the two outcomes. -/
theorem error_cannot_be_omitted {waits : DirectedWaitTranslation successOrError successOnly}
    (conformance : Grass.ImplementationConformance successOrError successOnly id waits) : False := by
  obtain ⟨right, empty, related⟩ := conformance.finite.initialForth
    successOrErrorErrorInitial rfl
  obtain ⟨upperHistory, upperFinished, upperStarts, outcomes⟩ := terminal_counterpart_required conformance
    related (lowerHistory := successOrErrorErrorInitial) trivial (History.Extension.refl _)
  simp [successOrError, successOrErrorErrorInitial] at outcomes
  change false = true at outcomes
  cases outcomes

abbrev loopingSystem : RelationalSystem Unit where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := by
    intro a b c ab bc
    trivial
  stepExtends := by
    intro before state choice event next after step
    trivial

abbrev loopingNoWaitBoundary : loopingSystem.WaitBoundary noRequests where
  Occurrence := Empty
  request := fun occurrence => nomatch occurrence
  Pending := fun _ occurrence => nomatch occurrence
  Reply := fun occurrence => nomatch occurrence
  reply_unique := by
    intro occurrence
    exact nomatch occurrence
  nonterminal := by
    intro history occurrence
    exact nomatch occurrence
  step_reply := by
    intro history occurrence
    exact nomatch occurrence
  reply_step := by
    intro history occurrence
    exact nomatch occurrence

abbrev looping : BehaviorModel Bool where
  Event := Unit
  Observation := Unit
  observationProjection := { project := fun _ => [] }
  Request := Empty
  system := loopingSystem
  protocol := noRequests
  boundary := loopingNoWaitBoundary
  result := fun _ _ => none
  terminal_result := by simp [loopingSystem]
  terminal_no_step := by
    intro state graph terminal choice event next nextGraph step
    exact False.elim terminal

def loopingInitial : looping.History :=
  .initial (state := ()) (graph := ()) trivial

def loopingRun (history : looping.History) :
    looping.system.InfiniteContinuation history.state history.graph history.path.events where
  stateAt := fun _ => ()
  graphAt := fun _ => ()
  choiceAt := fun _ => ()
  eventAt := fun _ => ()
  stateZero := by cases history.state; rfl
  graphZero := by cases history.graph; rfl
  step := fun _ => trivial
  consistent := trivial

def loopingTranslation : DirectedWaitTranslation looping successOnly where
  request := fun request => nomatch request
  response := fun request => nomatch request
  allowed := by
    intro request
    exact nomatch request
  permanent := by
    intro request
    exact nomatch request

/-- The actual looping lower completion cannot be omitted by a terminal-only upper model. -/
theorem divergence_cannot_be_omitted
    (conformance : Grass.ImplementationConformance looping successOnly id loopingTranslation) : False := by
  obtain ⟨right, empty, related⟩ := conformance.finite.initialForth loopingInitial rfl
  obtain ⟨upperHistory, upperRun, upperStarts⟩ := infinite_counterpart_required conformance
    related (loopingRun loopingInitial) (History.Extension.refl _)
  exact no_infinite_success_only upperRun

abbrev waitProtocol : WaitProtocol Unit where
  Response := fun _ => Empty
  Allowed := fun _ response => nomatch response
  AllowsPermanentWait := fun _ => True

abbrev waitingSystem : RelationalSystem Unit where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => False
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := by
    intro a b c ab bc
    trivial
  stepExtends := by
    intro before state choice event next after step
    exact False.elim step

abbrev lowerWaitBoundary : waitingSystem.WaitBoundary waitProtocol where
  Occurrence := Unit
  request := fun _ => ()
  Pending := fun _ _ => True
  Reply := fun occurrence response => nomatch response
  reply_unique := by
    intro occurrence first second choice firstReply secondReply
    exact nomatch first
  nonterminal := by
    intro history occurrence pending terminal
    exact False.elim terminal
  step_reply := by
    intro history occurrence pending choice event next nextGraph step
    exact False.elim step
  reply_step := by
    intro history occurrence pending response allowed
    exact nomatch response

abbrev upperWaitBoundary : terminalSystem.WaitBoundary waitProtocol where
  Occurrence := Unit
  request := fun _ => ()
  Pending := fun _ _ => False
  Reply := fun occurrence response => nomatch response
  reply_unique := by
    intro occurrence first second choice firstReply secondReply
    exact nomatch first
  nonterminal := by
    intro history occurrence pending
    exact False.elim pending
  step_reply := by
    intro history occurrence pending
    exact False.elim pending
  reply_step := by
    intro history occurrence pending
    exact False.elim pending

abbrev waitingLower : BehaviorModel Bool where
  Event := Unit
  Observation := Unit
  observationProjection := { project := fun _ => [] }
  Request := Unit
  system := waitingSystem
  protocol := waitProtocol
  boundary := lowerWaitBoundary
  result := fun _ _ => none
  terminal_result := by simp [waitingSystem]
  terminal_no_step := by
    intro state graph terminal choice event next nextGraph step
    exact False.elim terminal

abbrev waitingUpper : BehaviorModel Bool where
  Event := Unit
  Observation := Unit
  observationProjection := { project := fun _ => [] }
  Request := Unit
  system := terminalSystem
  protocol := waitProtocol
  boundary := upperWaitBoundary
  result := fun _ _ => some true
  terminal_result := by simp [terminalSystem]
  terminal_no_step := by
    intro state graph terminal choice event next nextGraph step
    exact False.elim step

def waitingLowerInitial : waitingLower.History :=
  .initial (state := ()) (graph := ()) trivial

def waitingLowerWitness : PermanentWait waitingLower.boundary waitingLowerInitial where
  occurrence := ()
  pending := trivial
  permitted := trivial

def waitingTranslation : DirectedWaitTranslation waitingLower waitingUpper where
  request := id
  response := fun request response => nomatch response
  allowed := by
    intro request response
    exact nomatch response
  permanent := by
    intro request permitted
    trivial

/-- The actual permitted lower permanent wait cannot be omitted by an upper
boundary whose pending predicate is false. -/
theorem waiting_cannot_be_omitted
    (conformance : Grass.ImplementationConformance waitingLower waitingUpper id waitingTranslation) :
    False := by
  obtain ⟨right, empty, related⟩ := conformance.finite.initialForth waitingLowerInitial rfl
  obtain ⟨upperHistory, upperWaiting, upperStarts⟩ := waiting_counterpart_required conformance
    related waitingLowerWitness (History.Extension.refl _)
  exact upperWaiting.not_terminal trivial

/-- The upper error history is real, but directed conformance has no reverse
coverage field that would require a lower error counterpart. -/
theorem upper_error_is_terminal : successOrError.system.Terminal
    successOrErrorErrorInitial.state successOrErrorErrorInitial.graph := by
  trivial

end Grass.Tests.Refinement.ImplementationConformance
