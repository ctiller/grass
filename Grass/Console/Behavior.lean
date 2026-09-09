import Grass.Semantics.OutputCut
import Grass.Semantics.Waiting

/-!
# One bounded logical console interaction

This module describes one already-rendered request.  A pending cut is a frontier
in that one request, not an invitation to issue a replacement provider call.
In particular a partial advance preserves the same `payload` parameter.
-/

namespace Grass.Console.Behavior

open Grass.Std.Logical
open Grass.Semantics
open Grass.RelationalSystem

/-- The observable terminal classifications for one stdout interaction. -/
inductive TerminalCause where
  | success
  | writeFailed
  | noProgress
  | stdoutUnavailable
deriving DecidableEq

/-- A response to the residual frontier of the fixed request. -/
inductive Reply (payload : Vec Byte) (cut : OutputCut payload) where
  | advance (next : OutputCut payload) (strict : cut.offset < next.offset)
  | finish (cause : TerminalCause)

/-- The terminal causes which are legal at an exact cut. -/
def FinishAllowed {payload : Vec Byte} (cut : OutputCut payload) : TerminalCause → Prop
  | .success => cut.offset = payload.length
  | .writeFailed => True
  | .noProgress => cut.offset < payload.length
  | .stdoutUnavailable => cut.offset = 0

/-- All allowed provider replies at an exact residual-output frontier. -/
def ReplyAllowed {payload : Vec Byte} (cut : OutputCut payload) : Reply payload cut → Prop
  | .advance next _strict => cut.offset < next.offset
  | .finish cause => FinishAllowed cut cause

/-- The state keeps the exact committed cut after every partial result. -/
inductive State (payload : Vec Byte) where
  | pending (cut : OutputCut payload)
  | finished (cut : OutputCut payload) (cause : TerminalCause)

/-- An audit event either exposes the exact newly emitted byte segment or a cause. -/
inductive Event where
  | emitted (bytes : Vec Byte)
  | terminal (cause : TerminalCause)

/-! `Reply` is indexed by the current cut, while `RelationalSystem.Choice` is
one fixed type.  `Choice` keeps the current cut explicitly; `step` below is the
only place it is accepted, and thereby prevents a reply for another frontier. -/
inductive Choice (payload : Vec Byte) where
  | reply (cut : OutputCut payload) (response : Reply payload cut)

/-- The relational-system presentation has no evolving graph. -/
def system (payload : Vec Byte) : RelationalSystem Event where
  State := State payload
  Choice := Choice payload
  Graph := Unit
  Initial := fun state _ => state = .pending (OutputCut.zero payload)
  Step := fun _ state choice event next _ =>
    match choice with
    | .reply cut (.advance after _strict) =>
        state = .pending cut ∧ event = .emitted (cut.between after) ∧ next = .pending after
    | .reply cut (.finish cause) =>
        state = .pending cut ∧ FinishAllowed cut cause ∧ event = .terminal cause ∧
          next = .finished cut cause
  Terminal := fun state _ => ∃ cut cause, state = .finished cut cause ∧ FinishAllowed cut cause
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := Eq
  extendsRefl := fun _ => rfl
  extendsTrans := Eq.trans
  stepExtends := fun _ => rfl

/-- A direct classification of every actual transition; there are no pending
self-steps and no steps from a terminal state. -/
theorem step_iff {payload : Vec Byte} {before after : State payload} {choice : Choice payload}
    {event : Event} : (system payload).Step () before choice event after () ↔
      match choice with
      | .reply cut (.advance next _strict) =>
          before = .pending cut ∧ event = .emitted (cut.between next) ∧ after = .pending next
      | .reply cut (.finish cause) =>
          before = .pending cut ∧ FinishAllowed cut cause ∧ event = .terminal cause ∧
            after = .finished cut cause := Iff.rfl

/-- Initial pending state at the zero cut. -/
def initial (payload : Vec Byte) : (system payload).History :=
  History.initial (system := system payload) (state := .pending (OutputCut.zero payload))
    (graph := ()) rfl

/-- One positive advance from an arbitrary reachable frontier. -/
def advanceHistory (payload : Vec Byte) (before after : OutputCut payload)
    (strict : before.offset < after.offset)
    (history : (system payload).History)
    (located : history.state = .pending before) : (system payload).History :=
  history.append (.snoc .nil (Grass.Console.Behavior.Choice.reply before
      (Grass.Console.Behavior.Reply.advance after strict))
    (Event.emitted (before.between after)) (Grass.Console.Behavior.State.pending after) () (by
      rw [located]
      simp [system]))

/-- Every exact cut is reachable with zero steps at zero or one strictly positive advance. -/
def pendingAt (payload : Vec Byte) (cut : OutputCut payload) : (system payload).History :=
  if zero : cut = OutputCut.zero payload then
    cast (by subst cut; rfl) (initial payload)
  else
    advanceHistory payload (OutputCut.zero payload) cut (by
      simp [OutputCut.zero]
      exact Nat.pos_of_ne_zero (fun h => zero (OutputCut.ext h))) (initial payload) rfl

theorem pendingAt_state (payload : Vec Byte) (cut : OutputCut payload) :
    (pendingAt payload cut).state = .pending cut := by
  unfold pendingAt
  split <;> rename_i zero
  · cases zero
    rfl
  · change (advanceHistory payload (OutputCut.zero payload) cut _ (initial payload) rfl).state = _
    unfold advanceHistory History.append
    rfl

/-- The exact emitted bytes in an event trace; terminal events contribute none. -/
def emittedBytes : List Event → Vec Byte
  | [] => Vec.empty
  | .emitted bytes :: rest => bytes ++ emittedBytes rest
  | .terminal _ :: rest => emittedBytes rest

theorem emittedBytes_append (left right : List Event) :
    emittedBytes (left ++ right) = emittedBytes left ++ emittedBytes right := by
  induction left with
  | nil => simp [emittedBytes]
  | cons event rest ih =>
    cases event <;> simp [emittedBytes, ih, Vec.append_assoc]

/-- The request and reply vocabulary for local residual-frontier waiting. -/
def protocol (payload : Vec Byte) : WaitProtocol (OutputCut payload) where
  Response := Reply payload
  Allowed := ReplyAllowed
  AllowsPermanentWait := fun _ => True

/-- A boundary occurrence denotes the current residual frontier in this one
logical request.  It is explicitly not a fresh provider-call occurrence. -/
def boundary (payload : Vec Byte) : (system payload).WaitBoundary (protocol payload) where
  Occurrence := OutputCut payload
  request := id
  Pending := fun history cut => history.state = .pending cut
  Reply := fun cut response choice => choice = .reply cut response
  reply_unique := by
    intro _ first second choice left right
    have equal : Choice.reply _ first = Choice.reply _ second := left.symm.trans right
    cases equal
    rfl
  nonterminal := by
    intro history cut located ⟨terminalCut, cause, equal, allowed⟩
    rw [located] at equal
    cases equal
  step_reply := by
    intro history cut located choice event next nextGraph step
    rcases choice with ⟨choiceCut, response⟩
    cases response with
    | advance after strict =>
      rcases (step_iff.mp step) with ⟨origin, _, _⟩
      have same : State.pending cut = State.pending choiceCut := located.symm.trans origin
      cases same
      exact ⟨.advance after strict, strict, rfl⟩
    | finish cause =>
      rcases (step_iff.mp step) with ⟨origin, allowed, _, _⟩
      have same : State.pending cut = State.pending choiceCut := located.symm.trans origin
      cases same
      exact ⟨.finish cause, allowed, rfl⟩
  reply_step := by
    intro history cut located response allowed
    cases response with
    | advance after strict =>
      refine ⟨.reply cut (.advance after strict), .emitted (cut.between after), .pending after,
        (), rfl, ?_⟩
      rw [located]
      simp [system]
    | finish cause =>
      refine ⟨.reply cut (.finish cause), .terminal cause, .finished cut cause, (), rfl, ?_⟩
      rw [located]
      exact ⟨rfl, allowed, rfl, rfl⟩

/-- Every reachable pending cut has a permanent-wait witness and retains all its
allowed replies. -/
def permanentWaitAt (payload : Vec Byte) (cut : OutputCut payload) :
    PermanentWait (boundary payload) (pendingAt payload cut) :=
  ⟨cut, pendingAt_state payload cut, trivial⟩

/-- Public reachability law for every exact byte cut, including interior UTF-8
and newline positions supplied by a rendering layer. -/
theorem every_cut_reachable (payload : Vec Byte) (cut : OutputCut payload) :
    (pendingAt payload cut).state = .pending cut :=
  pendingAt_state payload cut

/-- Public permanent-wait witness at the same residual-output occurrence. -/
def wait_at_cut (payload : Vec Byte) (cut : OutputCut payload) :
    PermanentWait (boundary payload) (pendingAt payload cut) :=
  permanentWaitAt payload cut

/-- A strictly decreasing finite rank for every concrete transition.  Waiting is
not a transition, so it does not manufacture a fake self-step. -/
def rank {payload : Vec Byte} : State payload → Nat
  | .pending cut => cut.remaining.length + 1
  | .finished _ _ => 0

theorem step_rank_decreases {payload : Vec Byte} {before after : State payload}
    {choice : Choice payload} {event : Event}
    (step : (system payload).Step () before choice event after ()) : rank after < rank before := by
  rcases choice with ⟨cut, response⟩
  cases response with
  | advance next strict =>
    rcases (step_iff.mp step) with ⟨origin, eventEq, nextEq⟩
    subst before
    subst after
    simp only [rank]
    exact Nat.succ_lt_succ (OutputCut.remaining_decreases cut next strict)
  | finish cause =>
    rcases (step_iff.mp step) with ⟨origin, allowed, eventEq, nextEq⟩
    subst before
    subst after
    simp [rank]

/-- Finishing from a pending cut is possible exactly for the stated cause law. -/
theorem finish_possible {payload : Vec Byte} (history : (system payload).History)
    (cut : OutputCut payload) (located : history.state = .pending cut) (cause : TerminalCause) :
    FinishAllowed cut cause ↔ ∃ event next,
      (system payload).Step history.graph history.state (.reply cut (.finish cause)) event next () := by
  constructor
  · intro allowed
    exact ⟨.terminal cause, .finished cut cause, by simp [system, located, allowed]⟩
  · rintro ⟨event, next, step⟩
    exact (step_iff.mp step).2.1

end Grass.Console.Behavior
