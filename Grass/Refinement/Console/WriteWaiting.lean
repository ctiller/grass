import Grass.Refinement.Console.WriteHistory
import Grass.Semantics.Waiting

/-!
# Permanent waiting in the portable write model

The existing adapter retains one exact occurrence at each external effect.
This interpretation proves that its outgoing steps deliver replies to that
occurrence and that every dependent reply remains possible. Permission for
permanent nonresponse is an explicit protocol parameter, not a consequence of
the adapter's held bag. A future captured console contract must supply that
exact permission; this is not a provider or whole-program certificate.
-/

namespace Grass.Refinement.Console.WriteWaiting

open Grass.Process Grass.Std.Logical Grass.Std.Console Grass.Std.Console.WriteProcess
open Grass.RelationalSystem
open WriteHistory

/-- All dependent replies of the existing model are allowed; nonresponse is
selected explicitly and must ultimately be supplied by the captured contract. -/
def protocol {payload : Vec Byte} (mayWait : Demand payload → Prop) :
    WaitProtocol (Demand payload) where
  Response := Demand.Result
  Allowed := fun _ _ => True
  AllowsPermanentWait := mayWait

/-- The portable model's exact single-occurrence external boundary. -/
def boundary {payload : Vec Byte} (mayWait : Demand payload → Prop) :
    (system payload).WaitBoundary (protocol mayWait) where
  Occurrence := (machine payload).Occurrence
  request := fun occurrence => occurrence.demand
  Pending := fun history occurrence => (machine payload).held history.state = {occurrence}
  Reply := fun occurrence response choice => choice = .result occurrence response
  reply_unique := by
    intro occurrence first second choice left right
    have equal := left.symm.trans right
    cases equal
    rfl
  nonterminal := by
    intro history occurrence held terminal
    obtain ⟨result, decision⟩ := terminal
    have empty := SequentialMachine.held_of_terminal decision
    rw [held] at empty
    have cards := congrArg Bag.card empty
    simp [Bag.singleton_eq] at cards
  step_reply := by
    intro history occurrence held choice event next nextGraph step
    obtain ⟨_, _, drives⟩ := step
    cases choice with
    | internal =>
        have empty := SequentialMachine.held_of_internal drives
        rw [held] at empty
        have cards := congrArg Bag.card empty
        simp [Bag.singleton_eq] at cards
    | result actual response =>
        have same : actual = occurrence := by
          have bags := drives.1.symm.trans held
          have mem : actual ∈ ({occurrence} : Bag (machine payload).Occurrence) := by
            rw [← bags]; simp
          simpa using mem
        subst actual
        exact ⟨response, trivial, rfl⟩
  reply_step := by
    intro history occurrence held response _
    refine ⟨.result occurrence response, [],
      ⟨history.state.age + 1, occurrence.resume response⟩, (), rfl, ?_⟩
    exact ⟨rfl, rfl, held, rfl, rfl⟩

/-- A held occurrence admits a permanent wait precisely when the selected
protocol permits nonresponse at that demand. No transition is added. -/
def waitOfHeld {payload : Vec Byte} {mayWait : Demand payload → Prop}
    (history : (system payload).History) (occurrence : (machine payload).Occurrence)
    (held : (machine payload).held history.state = {occurrence})
    (permitted : mayWait occurrence.demand) : PermanentWait (boundary mayWait) history :=
  ⟨occurrence, held, permitted⟩

/-- Waiting retains the same age, state, demand and continuation occurrence. -/
theorem wait_occurrence_exact {payload : Vec Byte} {mayWait : Demand payload → Prop}
    {history : (system payload).History} (waiting : PermanentWait (boundary mayWait) history) :
    waiting.occurrence.point = history.state ∧
      (machine payload).held history.state = {waiting.occurrence} := by
  refine ⟨?_, waiting.pending⟩
  apply SequentialMachine.held_point
  change waiting.occurrence ∈ (machine payload).held history.state
  have held : (machine payload).held history.state = {waiting.occurrence} := waiting.pending
  rw [held]
  exact Bag.mem_singleton.mpr rfl

/-- Existing finite accounting applies unchanged at a permanently waiting
frontier; this does not manufacture an infinite observation stream. -/
theorem wait_prefix {payload : Vec Byte} {mayWait : Demand payload → Prop}
    {history : (system payload).History} (_waiting : PermanentWait (boundary mayWait) history) :
    ∃ count, count ≤ payload.length ∧
      historyBytes history.path.events = payload.take count :=
  run_prefix history.erase

/-- The concrete reply interpretation forbids an internal step at any held
external occurrence. It cannot disguise spinning as external nonresponse. -/
theorem wait_no_internal_step {payload : Vec Byte} {mayWait : Demand payload → Prop}
    {history : (system payload).History} (waiting : PermanentWait (boundary mayWait) history)
    (events : List (Vec Byte)) (next : (system payload).State) (graph : Unit) :
    ¬ (system payload).Step history.graph history.state .internal events next graph := by
  intro step
  obtain ⟨response, _, reply⟩ :=
    (boundary mayWait).step_reply history waiting.occurrence waiting.pending
      .internal events next graph step
  change (DirectEvent.internal : (machine payload).Event) =
    DirectEvent.result waiting.occurrence response at reply
  cases reply

/-- Initial acquisition of stdout, with no prior choices or events. -/
def initialHistory (payload : Vec Byte) : (system payload).History :=
  History.initial (system := system payload) (graph := ()) ⟨rfl, rfl, rfl⟩

/-- The exact initial stdout occurrence generated by the adapter. -/
def stdoutOccurrence (payload : Vec Byte) : (machine payload).Occurrence :=
  ⟨(initialHistory payload).state, .stdout, fun available =>
    match available with
    | true => .writing (startCursor payload)
    | false => .unavailable⟩

/-- The initial occurrence is the one actually held, not a reconstructed call. -/
theorem stdout_held (payload : Vec Byte) :
    (machine payload).held (initialHistory payload).state = {stdoutOccurrence payload} := rfl

/-- Consume the actual successful stdout reply to reach the first write. -/
def readyHistory (payload : Vec Byte) : (system payload).History :=
  (initialHistory payload).append
    (Path.snoc (system := system payload) .nil (.result (stdoutOccurrence payload) true) []
      ⟨1, .writing (startCursor payload)⟩ () ⟨rfl, rfl, stdout_held payload, rfl, rfl⟩)

/-- The first write's exact occurrence, retaining its generated age and resume. -/
def writeOccurrence (payload : Vec Byte) (nonempty : 0 < payload.length) :
    (machine payload).Occurrence :=
  ⟨(readyHistory payload).state, .write (startCursor payload),
    fun response => .publish (startCursor payload) nonempty response⟩

/-- For every nonempty payload, the successful acquisition history reaches
the actual first write occurrence. -/
theorem write_held (payload : Vec Byte) (nonempty : 0 < payload.length) :
    (machine payload).held (readyHistory payload).state = {writeOccurrence payload nonempty} := by
  apply SequentialMachine.held_of_effect
  change WriteProcess.decide (.writing (startCursor payload)) = _
  simp only [WriteProcess.decide]
  exact dif_pos nonempty

/-- A complete permanent-write wait for every nonempty payload, conditional
only on this exact request's selected protocol permission. -/
def waitingAtWrite (payload : Vec Byte) (nonempty : 0 < payload.length)
    (mayWait : Demand payload → Prop) (permitted : mayWait (.write (startCursor payload))) :
    CompleteHistory (boundary mayWait) :=
  .waiting (readyHistory payload)
    (waitOfHeld _ (writeOccurrence payload nonempty) (write_held payload nonempty) permitted)

end Grass.Refinement.Console.WriteWaiting
