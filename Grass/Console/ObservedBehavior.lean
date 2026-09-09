import Grass.Console.LineBehavior
import Grass.Console.Accounting
import Grass.Semantics.BoundaryTiming
import Grass.Semantics.BehaviorModel

/-!
# Console completion through committed observation

This is the concrete status-bearing console wrapper.  A write result selects a
fixed reporting record; a later abstract observation commits that already
selected result. `reporting_step_exact` proves reporting cannot emit more bytes
or revise the selection.
-/

namespace Grass.Console.ObservedBehavior

open Grass.Std.Logical Grass.Semantics Grass.RelationalSystem
open Grass.Console
open Grass.Specification

variable {Outcome : Type}

/-- The exact result selected by the component write interaction. -/
structure Selection (request : LineRequest Outcome) (rendering : LineRendering) where
  cut : OutputCut (rendering.bytes request.line)
  cause : Behavior.TerminalCause
  allowed : Behavior.FinishAllowed cut cause

/-- The public outcome is derived from the captured request policy. -/
def Selection.publicOutcome {request : LineRequest Outcome} {rendering : LineRendering}
    (selection : Selection request rendering) : Outcome :=
  request.outcome selection.cause

inductive State (request : LineRequest Outcome) (rendering : LineRendering) where
  | writing (cut : OutputCut (rendering.bytes request.line))
  | reporting (selection : Selection request rendering)
  | observed (selection : Selection request rendering)

inductive Event (request : LineRequest Outcome) (rendering : LineRendering) where
  | emitted (bytes : Vec Byte)
  | reported (selection : Selection request rendering)
  | observed (selection : Selection request rendering)

inductive Choice (request : LineRequest Outcome) (rendering : LineRendering) where
  | output (cut : OutputCut (rendering.bytes request.line))
      (reply : Behavior.Reply (rendering.bytes request.line) cut)
  | observe (selection : Selection request rendering) (reply : Unit)

def system (request : LineRequest Outcome) (rendering : LineRendering) :
    RelationalSystem (Event request rendering) where
  State := State request rendering
  Choice := Choice request rendering
  Graph := Unit
  Initial := fun state _ => state = .writing (OutputCut.zero _)
  Step := fun _ state choice event next _ =>
    match choice with
    | .output cut (.advance after _strict) =>
        state = .writing cut ∧ event = .emitted (cut.between after) ∧ next = .writing after
    | .output cut (.finish cause) =>
        ∃ allowed : Behavior.FinishAllowed cut cause,
          state = .writing cut ∧ event = .reported ⟨cut, cause, allowed⟩ ∧
            next = .reporting ⟨cut, cause, allowed⟩
    | .observe selection _ =>
        state = .reporting selection ∧ event = .observed selection ∧ next = .observed selection
  Terminal := fun state _ => ∃ selection, state = .observed selection
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := Eq
  extendsRefl := fun _ => rfl
  extendsTrans := Eq.trans
  stepExtends := fun _ => rfl

def initial (request : LineRequest Outcome) (rendering : LineRendering) :
    (system request rendering).History :=
  History.initial (system := system request rendering)
    (state := .writing (OutputCut.zero _)) (graph := ()) rfl

/-- Output frontiers and reporting observations are different request kinds. -/
inductive Request (request : LineRequest Outcome) (rendering : LineRendering) where
  | output (cut : OutputCut (rendering.bytes request.line))
  | observation (selection : Selection request rendering)

def protocol (request : LineRequest Outcome) (rendering : LineRendering) :
    WaitProtocol (Request request rendering) where
  Response
    | .output cut => Behavior.Reply _ cut
    | .observation _ => Unit
  Allowed
    | .output cut, reply => Behavior.ReplyAllowed cut reply
    | .observation _, _ => True
  AllowsPermanentWait := fun _ => True

def boundary (request : LineRequest Outcome) (rendering : LineRendering) :
    (system request rendering).WaitBoundary (protocol request rendering) where
  Occurrence := Request request rendering
  request := id
  Pending := fun history occurrence => match occurrence with
    | .output cut => history.state = .writing cut
    | .observation selection => history.state = .reporting selection
  Reply := fun occurrence response choice => match occurrence with
    | .output cut => choice = .output cut response
    | .observation selection => choice = .observe selection response
  reply_unique := by
    intro occurrence first second choice left right
    cases occurrence with
    | output cut =>
      have equal := left.symm.trans right
      cases equal
      rfl
    | observation selection => cases first; cases second; rfl
  nonterminal := by
    intro history occurrence pending terminal
    rcases terminal with ⟨selection, terminal⟩
    cases occurrence <;> simp_all
  step_reply := by
    intro history occurrence pending choice event next nextGraph step
    cases occurrence with
    | output cut =>
      cases choice with
      | output choiceCut response =>
        cases response with
        | advance after strict =>
          simp only [system] at step
          rcases step with ⟨origin, _, _⟩
          cases pending.symm.trans origin
          exact ⟨.advance after strict, strict, rfl⟩
        | finish cause =>
          simp only [system] at step
          rcases step with ⟨allowed, origin, _, _⟩
          cases pending.symm.trans origin
          exact ⟨.finish cause, allowed, rfl⟩
      | observe selection reply =>
        change history.state = .writing cut at pending
        rcases step with ⟨origin, _, _⟩
        rw [pending] at origin
        cases origin
    | observation selection =>
      cases choice with
      | output cut response =>
        change history.state = .reporting selection at pending
        cases response with
        | advance after strict =>
          rcases step with ⟨origin, _, _⟩
          rw [pending] at origin
          cases origin
        | finish cause =>
          rcases step with ⟨allowed, origin, _, _⟩
          rw [pending] at origin
          cases origin
      | observe choiceSelection reply =>
        simp only [system] at step
        rcases step with ⟨origin, _, _⟩
        cases pending.symm.trans origin
        exact ⟨reply, trivial, rfl⟩
  reply_step := by
    intro history occurrence pending response allowed
    cases occurrence with
    | output cut =>
      cases response with
      | advance after strict =>
        exact ⟨.output cut (.advance after strict), .emitted (cut.between after),
          .writing after, (), rfl, pending ▸ ⟨rfl, rfl, rfl⟩⟩
      | finish cause =>
        let selection : Selection request rendering := ⟨cut, cause, allowed⟩
        exact ⟨.output cut (.finish cause), .reported selection, .reporting selection,
          (), rfl, ⟨allowed, pending, rfl, rfl⟩⟩
    | observation selection =>
      cases response
      exact ⟨.observe selection (), .observed selection, .observed selection,
        (), rfl, pending ▸ ⟨rfl, rfl, rfl⟩⟩

/-- `BehaviorModel.terminal_result` identifies outcome availability with committed observation. -/
def model (request : LineRequest Outcome) (rendering : LineRendering) :
    BehaviorModel Outcome where
  Event := Event request rendering
  Observation := Event request rendering
  observationProjection := .identity _
  Request := Request request rendering
  system := system request rendering
  protocol := protocol request rendering
  boundary := boundary request rendering
  result := fun state _ => match state with
    | .observed selection => some selection.publicOutcome
    | _ => none
  terminal_result := by
    intro state graph
    cases state with
    | writing cut => simp [system]
    | reporting selection => simp [system]
    | observed selection => simp [system, Selection.publicOutcome]
  terminal_no_step := by
    intro state graph terminal choice event next nextGraph step
    rcases terminal with ⟨selection, stateEq⟩
    subst state
    cases choice with
    | output cut response => cases response <;> simp [system] at step
    | observe selected reply => simp [system] at step

theorem advanceStep (request : LineRequest Outcome) (rendering : LineRendering)
    (before after : OutputCut (rendering.bytes request.line))
    (strict : before.offset < after.offset) :
    (system request rendering).Step () (.writing before)
      (Choice.output before (.advance after strict)) (.emitted (before.between after))
      (.writing after) () := ⟨rfl, rfl, rfl⟩

theorem reportStep (request : LineRequest Outcome) (rendering : LineRendering)
    (selection : Selection request rendering) :
    (system request rendering).Step () (.writing selection.cut)
      (Choice.output selection.cut (.finish selection.cause)) (.reported selection)
      (.reporting selection) () := ⟨selection.allowed, rfl, rfl, rfl⟩

theorem observeStep (request : LineRequest Outcome) (rendering : LineRendering)
    (selection : Selection request rendering) :
    (system request rendering).Step () (.reporting selection)
      (Choice.observe selection ()) (.observed selection) (.observed selection) () :=
  ⟨rfl, rfl, rfl⟩

/-- A reachable history at every exact output frontier. -/
def writingAt (request : LineRequest Outcome) (rendering : LineRendering)
    (cut : OutputCut (rendering.bytes request.line)) : (system request rendering).History :=
  if zero : cut = OutputCut.zero _ then
    cast (by subst cut; rfl) (initial request rendering)
  else
    let strict : (OutputCut.zero _).offset < cut.offset := by
      simp [OutputCut.zero]
      exact Nat.pos_of_ne_zero (fun h => zero (OutputCut.ext h))
    let path : (system request rendering).Path
        (.writing (OutputCut.zero _)) () (.writing cut) () :=
      .snoc (Path.nil : (system request rendering).Path
        (.writing (OutputCut.zero _)) () (.writing (OutputCut.zero _)) ())
        (Choice.output (OutputCut.zero _) (.advance cut strict))
        (Event.emitted ((OutputCut.zero _).between cut)) (State.writing cut) ()
        (advanceStep request rendering _ cut strict)
    ⟨.writing (OutputCut.zero _), (), .writing cut, (), rfl, path⟩

@[simp] theorem writingAt_state (request : LineRequest Outcome) (rendering : LineRendering)
    (cut : OutputCut (rendering.bytes request.line)) :
    (writingAt request rendering cut).state = .writing cut := by
  unfold writingAt
  split <;> rename_i zero
  · cases zero
    rfl
  · rfl

/-- A permanent output wait at any reached byte cut, including the full cut. -/
def writingWait (request : LineRequest Outcome) (rendering : LineRendering)
    (cut : OutputCut (rendering.bytes request.line)) :
    PermanentWait (boundary request rendering) (writingAt request rendering cut) :=
  ⟨.output cut, writingAt_state request rendering cut, trivial⟩

/-- A concrete reporting history for every legal component terminal selection. -/
def reportingAt (request : LineRequest Outcome) (rendering : LineRendering)
    (selection : Selection request rendering) : (system request rendering).History :=
  (writingAt request rendering selection.cut).append
    (.snoc .nil (Choice.output selection.cut (.finish selection.cause))
    (Event.reported selection) (State.reporting selection) ()
    (writingAt_state _ _ _ ▸ reportStep request rendering selection))

@[simp] theorem reportingAt_state (request : LineRequest Outcome) (rendering : LineRendering)
    (selection : Selection request rendering) :
    (reportingAt request rendering selection).state = .reporting selection := rfl

def observe (request : LineRequest Outcome) (rendering : LineRendering)
    (selection : Selection request rendering) : (system request rendering).History :=
  (reportingAt request rendering selection).append
    (.snoc .nil (Choice.observe selection ()) (Event.observed selection) (State.observed selection) ()
      (reportingAt_state _ _ _ ▸ observeStep request rendering selection))

theorem observe_terminal (request : LineRequest Outcome) (rendering : LineRendering)
    (selection : Selection request rendering) :
    (system request rendering).Terminal (observe request rendering selection).state () :=
  ⟨selection, rfl⟩

/-- Reporting can wait forever at the fixed selection. -/
def reportingWait (request : LineRequest Outcome) (rendering : LineRendering)
    (selection : Selection request rendering) :
    PermanentWait (boundary request rendering) (reportingAt request rendering selection) :=
  ⟨.observation selection, rfl, trivial⟩

/-- Before the reporting selection, no observation request is pending. -/
theorem no_observation_while_writing {request : LineRequest Outcome}
    {rendering : LineRendering} {history : (system request rendering).History}
    {cut} {selection : Selection request rendering}
    (writing : history.state = .writing cut) :
    ¬ (boundary request rendering).Pending history (.observation selection) := by
  intro reporting
  change history.state = .reporting selection at reporting
  rw [writing] at reporting
  cases reporting

/-- Failure remains selectable after the complete payload has been emitted. -/
def fullCutFailure (request : LineRequest Outcome) (rendering : LineRendering) :
    Selection request rendering :=
  ⟨OutputCut.full _, .writeFailed, trivial⟩

/-- Every reporting selection comes from an actual terminal component history. -/
theorem reporting_has_component_terminal (request : LineRequest Outcome)
    (rendering : LineRendering) (selection : Selection request rendering) :
    ∃ history : (Behavior.system (rendering.bytes request.line)).History,
      history.state = .finished selection.cut selection.cause ∧
      Behavior.FinishAllowed selection.cut selection.cause := by
  let pending := Behavior.pendingAt (rendering.bytes request.line) selection.cut
  have transition : (Behavior.system (rendering.bytes request.line)).Step ()
      (.pending selection.cut)
      (Behavior.Choice.reply selection.cut (.finish selection.cause))
      (.terminal selection.cause) (.finished selection.cut selection.cause) () :=
    ⟨rfl, selection.allowed, rfl, rfl⟩
  let history := pending.append (.snoc .nil
    (Behavior.Choice.reply selection.cut (.finish selection.cause))
    (Behavior.Event.terminal selection.cause)
    (Behavior.State.finished selection.cut selection.cause) ()
    (Behavior.pendingAt_state _ _ ▸ transition))
  exact ⟨history, rfl, selection.allowed⟩

/-- The finite rank counts the remaining write budget and the two final phases. -/
def rank {request : LineRequest Outcome} {rendering : LineRendering} :
    State request rendering → Nat
  | .writing cut => 2 * cut.remaining.length + 2
  | .reporting _ => 1
  | .observed _ => 0

theorem step_rank_decreases {request : LineRequest Outcome} {rendering : LineRendering}
    {before after : State request rendering} {choice : Choice request rendering}
    {event : Event request rendering} {beforeGraph afterGraph : Unit}
    (step : (system request rendering).Step beforeGraph before choice event after afterGraph) :
    rank after < rank before := by
  cases choice with
  | output cut response =>
    cases response with
    | advance next strict =>
      rcases step with ⟨origin, _, nextEq⟩
      subst before; subst after
      simp only [rank]
      have decreases := OutputCut.remaining_decreases cut next strict
      omega
    | finish cause =>
      rcases step with ⟨allowed, origin, _, nextEq⟩
      subst before; subst after
      simp only [rank]
      omega
  | observe selection reply =>
    rcases step with ⟨origin, _, nextEq⟩
    subst before; subst after
    simp [rank]

private theorem no_descent (sequence : Nat → Nat)
    (descends : ∀ index, sequence (index + 1) < sequence index) : False := by
  have never : ∀ value, Acc (· < ·) value → ∀ index, sequence index ≠ value := by
    intro value accessible
    induction accessible with
    | intro current _ ih =>
      intro index equal
      exact ih (sequence (index + 1)) (equal ▸ descends index) (index + 1) rfl
  exact never (sequence 0) (Nat.lt_wfRel.wf.apply (sequence 0)) 0 rfl

theorem no_infinite_continuation {request : LineRequest Outcome}
    {rendering : LineRendering} {state : State request rendering} {graph : Unit}
    {priorEvents : List (Event request rendering)}
    (continuation : (system request rendering).InfiniteContinuation state graph priorEvents) :
    False :=
  no_descent (fun index => rank (continuation.stateAt index))
    (fun index => step_rank_decreases (continuation.step index))

/-- Every reachable phase has a finite suffix to committed observation. -/
theorem completionAdequate (request : LineRequest Outcome) (rendering : LineRendering) :
    BoundaryTerminalAdequate (boundary request rendering) where
  complete := by
    intro history
    cases stateEq : history.state with
    | writing cut =>
      let selection : Selection request rendering := ⟨cut, .writeFailed, trivial⟩
      have report : (system request rendering).Step history.graph history.state
          (.output cut (.finish .writeFailed)) (.reported selection) (.reporting selection) () :=
        ⟨trivial, stateEq, rfl, rfl⟩
      have observed : (system request rendering).Step () (.reporting selection)
          (.observe selection ()) (.observed selection) (.observed selection) () :=
        observeStep request rendering selection
      exact ⟨⟨.observed selection, (),
        .snoc (.snoc .nil _ _ _ _ report) _ _ _ _ observed, ⟨selection, rfl⟩⟩⟩
    | reporting selection =>
      have observed : (system request rendering).Step history.graph history.state
          (.observe selection ()) (.observed selection) (.observed selection) () := by
        cases history.graph
        exact stateEq ▸ observeStep request rendering selection
      exact ⟨⟨.observed selection, (), .snoc .nil _ _ _ _ observed, ⟨selection, rfl⟩⟩⟩
    | observed selection =>
      exact ⟨⟨history.state, history.graph, .nil, ⟨selection, stateEq⟩⟩⟩

/-- Bytes committed by every phase; reporting and observation retain the selected cut. -/
def committed {request : LineRequest Outcome} {rendering : LineRendering} :
    State request rendering → Vec Byte
  | .writing cut => cut.emitted
  | .reporting selection => selection.cut.emitted
  | .observed selection => selection.cut.emitted

def emittedBytes {request : LineRequest Outcome} {rendering : LineRendering} :
    List (Event request rendering) → Vec Byte
  | [] => Vec.empty
  | .emitted bytes :: rest => bytes ++ emittedBytes rest
  | .reported _ :: rest => emittedBytes rest
  | .observed _ :: rest => emittedBytes rest

theorem emittedBytes_append {request : LineRequest Outcome} {rendering : LineRendering}
    (left right : List (Event request rendering)) :
    emittedBytes (left ++ right) = emittedBytes left ++ emittedBytes right := by
  induction left with
  | nil => simp [emittedBytes]
  | cons event rest ih => cases event <;> simp [emittedBytes, ih, Vec.append_assoc]

def Accounts {request : LineRequest Outcome} {rendering : LineRendering}
    (before after : State request rendering) (events : List (Event request rendering)) : Prop :=
  committed after = committed before ++ emittedBytes events

private theorem path_accounting_aux (request : LineRequest Outcome) (rendering : LineRendering)
    {before after : State request rendering} {beforeGraph afterGraph : Unit}
    (path : (system request rendering).Path before beforeGraph after afterGraph) :
    True ∧ Accounts before after path.events := by
  refine Path.rec (motive := fun after afterGraph path =>
    True ∧ Accounts before after path.events) ?_ ?_ path
  · exact ⟨trivial, by simp [Accounts, Path.events, emittedBytes]⟩
  · intro current currentGraph prior choice event next nextGraph transition ih
    cases choice with
    | output cut response =>
      cases response with
      | advance after strict =>
        rcases transition with ⟨origin, eventEq, nextEq⟩
        subst current; subst event; subst next
        refine ⟨trivial, ?_⟩
        unfold Accounts at ih ⊢
        have account := ih.2
        change cut.emitted = committed before ++ emittedBytes prior.events at account
        change after.emitted = committed before ++
          emittedBytes (prior.events ++ [.emitted (cut.between after)])
        rw [emittedBytes_append]
        simp only [emittedBytes, Vec.append_empty]
        rw [← OutputCut.advance_exact cut after (Nat.le_of_lt strict), account]
        exact Vec.append_assoc _ _ _
      | finish cause =>
        rcases transition with ⟨allowed, origin, eventEq, nextEq⟩
        subst current; subst event; subst next
        refine ⟨trivial, ?_⟩
        unfold Accounts at ih ⊢
        have account := ih.2
        change cut.emitted = committed before ++ emittedBytes prior.events at account
        change cut.emitted = committed before ++
          emittedBytes (prior.events ++ [.reported ⟨cut, cause, allowed⟩])
        rw [emittedBytes_append]
        simpa [emittedBytes] using account
    | observe selection reply =>
      rcases transition with ⟨origin, eventEq, nextEq⟩
      subst current; subst event; subst next
      refine ⟨trivial, ?_⟩
      unfold Accounts at ih ⊢
      have account := ih.2
      change selection.cut.emitted = committed before ++ emittedBytes prior.events at account
      change selection.cut.emitted = committed before ++
        emittedBytes (prior.events ++ [.observed selection])
      rw [emittedBytes_append]
      simpa [emittedBytes] using account

theorem history_accounting {request : LineRequest Outcome} {rendering : LineRendering}
    (history : (system request rendering).History) :
    emittedBytes history.path.events = committed history.state := by
  have accounting := (path_accounting_aux request rendering history.path).2
  have initial : history.initialState = .writing (OutputCut.zero _) := history.validInitial
  have empty : committed history.initialState = Vec.empty := by
    rw [initial]
    exact OutputCut.emitted_zero
  unfold Accounts at accounting
  rw [empty, Vec.empty_append] at accounting
  exact accounting.symm

/-- `reporting_step_exact` proves reporting's only step observes the same selection. -/
theorem reporting_step_exact {request : LineRequest Outcome} {rendering : LineRendering}
    (selection : Selection request rendering) {choice event next nextGraph}
    (step : (system request rendering).Step () (.reporting selection)
      choice event next nextGraph) :
    choice = .observe selection () ∧ event = .observed selection ∧
      next = .observed selection := by
  cases choice with
  | output cut response => cases response <;> simp [system] at step
  | observe selected reply =>
    rcases step with ⟨origin, eventEq, nextEq⟩
    cases origin
    cases reply
    exact ⟨rfl, eventEq, nextEq⟩

/-- Commit observation by appending one step to the exact reached reporting history. -/
def observeAt {request : LineRequest Outcome} {rendering : LineRendering}
    (history : (system request rendering).History) (selection : Selection request rendering)
    (located : history.state = .reporting selection) : (system request rendering).History :=
  history.append (.snoc (Path.nil : (system request rendering).Path
    history.state history.graph history.state history.graph)
    (Choice.observe selection ()) (Event.observed selection) (State.observed selection) ()
    (by cases history.graph; exact located ▸ observeStep request rendering selection))

theorem observeAt_terminal {request : LineRequest Outcome} {rendering : LineRendering}
    (history : (system request rendering).History) (selection : Selection request rendering)
    (located : history.state = .reporting selection) :
    (system request rendering).Terminal (observeAt history selection located).state
      (observeAt history selection located).graph := ⟨selection, rfl⟩

theorem observeAt_events {request : LineRequest Outcome} {rendering : LineRendering}
    (history : (system request rendering).History) (selection : Selection request rendering)
    (located : history.state = .reporting selection) :
    (observeAt history selection located).path.events = history.path.events ++ [.observed selection] := rfl

theorem observeAt_choices {request : LineRequest Outcome} {rendering : LineRendering}
    (history : (system request rendering).History) (selection : Selection request rendering)
    (located : history.state = .reporting selection) :
    (observeAt history selection located).path.choices = history.path.choices ++ [.observe selection ()] := rfl

end Grass.Console.ObservedBehavior
