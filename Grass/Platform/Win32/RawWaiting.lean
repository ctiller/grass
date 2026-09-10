import Grass.Platform.Win32.RawPrefix
import Grass.Semantics.BehaviorModel
import Grass.Platform.Win32.ProviderContract
import Grass.Platform.Win32.RawObservation

/-! Fixed waiting semantics for the selected synchronous external-provider domain.
Provider actions and endpoint settlements are external; caller CPU work is not.
The domain permits provider nonresponse without a fairness promise. Applicability
still requires every boundary law below on actual initialized raw histories;
these proof obligations do not establish themselves or native API adequacy. -/

namespace Grass.Platform.Win32.Raw
open Grass.Core Grass.Op Grass.Memory
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- The exact issued call and existing protocol record, including caller,
provider, request and loan identities. -/
structure WaitOccurrence where
  call : CallProtocol.CallId
  record : CallProtocol.Pending ApiRequest

namespace WaitOccurrence
/-- Active checked control and retained runtime exclude terminal archives. -/
structure Pending (occurrence : WaitOccurrence) (state : RawState) : Prop where
  control : state.control =
    .pending occurrence.call occurrence.record.caller occurrence.record.agent
  recorded : state.metadata.pending.lookup occurrence.call = some occurrence.record
  consistent : state.ControlConsistent
  runtime : ∃ runtime, state.calls.lookup occurrence.call = some runtime ∧
    runtime.MatchesRequest occurrence.record.request

/-- Pending control excludes terminal settlement even if tables retain the call. -/
theorem Pending.nonterminal {occurrence : WaitOccurrence} {state : RawState}
    (pending : occurrence.Pending state) :
    ¬ ∃ call status, state.control = .terminal call status := by
  rintro ⟨call, status, terminal⟩
  have impossible := pending.control.symm.trans terminal
  cases impossible

/-- Actual response choice for this call. ExitProcess settles terminally;
it never denotes an ABI return. The boundary additionally requires an actual
RawStep for this choice, event, endpoint and causal graph. -/
def ReplyFor (occurrence : WaitOccurrence) :
    (request : ApiRequest) → ProviderContract.ApiResponse request → Choice → Prop
  | .getStdHandle _, handle, .stdoutResult call gpr _ =>
      call = occurrence.call ∧ gpr .rax = handle
  | .writeFile _, response, .providerReturn call actual _ _ =>
      call = occurrence.call ∧ actual = response
  | .exitProcess status, (), .exitObservation call actual =>
      call = occurrence.call ∧ actual = status
  | _, _, _ => False

/-- Reply interpretation uses the retained request, not a reconstructed API. -/
def Reply (occurrence : WaitOccurrence) := occurrence.ReplyFor occurrence.record.request

/-- Fixed external agency for this synchronous backend. CPU and call-entry
choices are caller work, even if their observations are silent. -/
def External (occurrence : WaitOccurrence) : Choice → Prop
  | .providerService call agent _ => call = occurrence.call ∧ agent = occurrence.record.agent
  | .providerReturn call _ _ _ | .stdoutResult call _ _ | .exitObservation call _ =>
      call = occurrence.call
  | .cpu _ | .apiEntry _ _ => False

/-- The same actual choice cannot settle this occurrence with two responses. -/
theorem reply_unique (occurrence : WaitOccurrence)
    (first second : ProviderContract.ApiResponse occurrence.record.request) (choice : Choice)
    (one : occurrence.Reply first choice) (two : occurrence.Reply second choice) :
    first = second := by
  unfold Reply at one two
  generalize occurrence.record.request = request at first second one two
  cases request <;> cases choice <;> simp [ReplyFor] at one two ⊢
  · exact one.2.symm.trans two.2
  · exact one.2.symm.trans two.2
  · change Unit at first second
    cases first
    cases second
    rfl
end WaitOccurrence

/-- The selected backend makes no provider responsiveness promise. Actual
permission at a cut still needs fixed Pending and all WaitLaws; directed
complete conformance must match the captured specification's wait. -/
def waitProtocol (environment : ConsoleEnvironment) (realization : WriteFile.Realization)
    (interpretation : WriteFile.ReturnInterpretation) : WaitProtocol WaitOccurrence where
  Response occurrence := ProviderContract.ApiResponse occurrence.record.request
  Allowed occurrence := ProviderContract.Allowed environment realization interpretation
    occurrence.call occurrence.record occurrence.record.request
  AllowsPermanentWait _ := True

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
  {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
    (FreshSupply.initial : FreshSupply GrantTag)}


/-- Proofs required to interpret the fixed raw predicates as a wait boundary.
No field chooses a pending predicate, reply meaning, agency policy or model.
Response allowance classifies actual replies; it does not require every
permitted alternative to remain reachable after service progress. -/
structure WaitLaws : Prop where
  step_external : ∀ (history : (system loaded realization environment interpretation covered).History) (occurrence : WaitOccurrence), occurrence.Pending history.state.down →
    ∀ choice event next nextGraph,
    (system loaded realization environment interpretation covered).Step history.graph history.state choice event next nextGraph →
      occurrence.External choice
  step_pending_or_reply : ∀ (history : (system loaded realization environment interpretation covered).History) (occurrence : WaitOccurrence), occurrence.Pending history.state.down →
    ∀ choice event next nextGraph,
    ∀ step : (system loaded realization environment interpretation covered).Step history.graph history.state choice event next nextGraph,
      occurrence.Pending (history.append (.snoc .nil choice event next nextGraph step)).state.down ∨
      ∃ response, (waitProtocol environment realization interpretation).Allowed occurrence response ∧
        occurrence.Reply response choice
  reply_allowed : ∀ (history : (system loaded realization environment interpretation covered).History) (occurrence : WaitOccurrence), occurrence.Pending history.state.down →
    ∀ response choice event next nextGraph,
    (system loaded realization environment interpretation covered).Step history.graph history.state choice event next nextGraph →
    occurrence.Reply response choice → (waitProtocol environment realization interpretation).Allowed occurrence response
  reply_ends : ∀ (history : (system loaded realization environment interpretation covered).History) (occurrence : WaitOccurrence), occurrence.Pending history.state.down →
    ∀ response choice event next nextGraph,
    ∀ step : (system loaded realization environment interpretation covered).Step history.graph history.state choice event next nextGraph,
    occurrence.Reply response choice →
      ¬ occurrence.Pending (history.append (.snoc .nil choice event next nextGraph step)).state.down

  /-- Some actual settlement remains possible from this cut. This does not
  promise every allowed alternative, nor force an execution to take that path. -/
  reply_possible : ∀ (history : (system loaded realization environment interpretation covered).History)
    (occurrence : WaitOccurrence), occurrence.Pending history.state.down →
    ∃ response, (waitProtocol environment realization interpretation).Allowed occurrence response ∧
      ∃ state graph, ∃ beforeReply : (system loaded realization environment interpretation covered).Path
        history.state history.graph state graph,
        (∀ choice ∈ beforeReply.choices, ∀ earlier, ¬ occurrence.Reply earlier choice) ∧
        occurrence.Pending (history.append beforeReply).state.down ∧
        ∃ choice event next nextGraph, occurrence.Reply response choice ∧
          (system loaded realization environment interpretation covered).Step
            graph state choice event next nextGraph

/-- A broken handoff with no possible outgoing step cannot use the fixed raw
waiting interpretation. Possibility of settlement is distinct from fairness. -/
theorem WaitLaws.not_pending_of_stuck
    (laws : WaitLaws (loaded := loaded) (realization := realization)
      (environment := environment) (interpretation := interpretation) (covered := covered))
    (history : (system loaded realization environment interpretation covered).History)
    (stuck : ∀ choice event next nextGraph,
      ¬ (system loaded realization environment interpretation covered).Step
        history.graph history.state choice event next nextGraph)
    (occurrence : WaitOccurrence) : ¬ occurrence.Pending history.state.down := by
  intro pending
  obtain ⟨response, allowed, state, graph, path, quiet, retained,
    choice, event, next, nextGraph, reply, step⟩ := laws.reply_possible history occurrence pending
  have same : ∀ {state graph},
      (system loaded realization environment interpretation covered).Path
        history.state history.graph state graph → state = history.state ∧ graph = history.graph := by
    intro state graph path
    induction path with
    | nil => exact ⟨rfl, rfl⟩
    | snoc prior choice event next nextGraph step ih =>
      exact False.elim (stuck choice event next nextGraph (by simpa [ih.1, ih.2] using step))
  obtain ⟨stateEq, graphEq⟩ := same path
  exact stuck choice event next nextGraph (by simpa [stateEq, graphEq] using step)


/-- The canonical boundary uses only fixed predicates and actual raw histories. -/
def waitBoundary (laws : WaitLaws (loaded := loaded) (realization := realization)
    (environment := environment) (interpretation := interpretation) (covered := covered)) :
    (system loaded realization environment interpretation covered).WaitBoundary (waitProtocol environment realization interpretation) where
  Occurrence := WaitOccurrence
  request := id
  Pending history occurrence := occurrence.Pending history.state.down
  External := WaitOccurrence.External
  Reply := WaitOccurrence.Reply
  reply_unique := WaitOccurrence.reply_unique
  nonterminal _ _ pending := pending.nonterminal
  step_external := laws.step_external
  step_pending_or_reply := laws.step_pending_or_reply
  reply_allowed := laws.reply_allowed
  reply_ends := laws.reply_ends

/-- The fixed complete raw domain. Laws discharge boundary applicability;
they do not alter raw transitions, initial states, observations or outcomes. -/
def behaviorModel (laws : WaitLaws (loaded := loaded) (realization := realization)
    (environment := environment) (interpretation := interpretation) (covered := covered)) :
    BehaviorModel (CallProtocol.CallId × BitVec 32) where
  Event := ULift.{1} Event
  Observation := Observation
  observationProjection := observationProjection
  Request := WaitOccurrence
  system := system loaded realization environment interpretation covered
  protocol := waitProtocol environment realization interpretation
  boundary := waitBoundary laws
  result state _ := result state.down
  terminal_result := terminal_result loaded realization environment interpretation covered
  terminal_no_step := terminal_no_step

end Grass.Platform.Win32.Raw
