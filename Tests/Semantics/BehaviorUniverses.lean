import Grass.Refinement.ImplementationConformance
import Grass.Semantics.Environment
import Grass.Platform.Win32.RawStepSignature

/-! Universe-carrier regressions. The high model below is not a RawStep model
or a claim about Windows waiting: its all-true relation only makes the public
semantic carriers inhabited while retaining the actual raw choice/event/graph
types that require the higher universe. -/
namespace Grass.Tests.Semantics.BehaviorUniverses

open Grass RelationalSystem
open Grass.Platform.Win32

private abbrev HighEvent := ULift.{1} Raw.Event
private abbrev HighState := ULift.{1} Nat
private abbrev HighGraph := ULift.{1} Raw.Graph

private def highSystem : RelationalSystem.{1} HighEvent where
  State := HighState
  Choice := Raw.Choice
  Graph := HighGraph
  Initial := fun _ _ => True
  Step := fun _ state _ _ next _ => next.down = state.down + 1
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

/-- Requests remain in `Type`, while a request's response is permitted in
`Type 1` without lifting the request carrier. -/
private def highProtocol : WaitProtocol.{0, 1} Unit where
  Response := fun _ => ULift.{1} Unit
  Allowed := fun _ _ => True
  AllowsPermanentWait := fun _ => True

private def highBoundary : highSystem.WaitBoundary.{1, 0, 1, 0} highProtocol where
  Occurrence := Nat
  request := fun _ => ()
  Pending := fun history occurrence => history.state.down = occurrence
  External := fun _ _ => True
  Reply := fun _ _ _ => True
  reply_unique := by
    intro _ first second _ _ _
    cases first
    cases second
    rfl
  nonterminal := by simp [highSystem]
  step_external := by intros; trivial
  step_pending_or_reply := by intros; right; exact ⟨.up (), trivial, trivial⟩
  reply_allowed := by intros; trivial
  reply_ends := by
    intro history occurrence pending response choice event next nextGraph step reply later
    change next.down = occurrence at later
    change next.down = history.state.down + 1 at step
    omega
  reply_path := by
    intro history occurrence pending response allowed
    exact ⟨history.state, history.graph, .nil, by intros; contradiction, pending,
      .cpu (.interruption 0), .up { memory := [], boundaries := [], kind := .internal },
      .up (history.state.down + 1), history.graph, trivial, rfl⟩

private def high : BehaviorModel.{1, 0, 1, 0} Empty where
  Event := HighEvent
  Observation := Unit
  observationProjection := { project := fun _ => [] }
  Request := Unit
  system := highSystem
  protocol := highProtocol
  boundary := highBoundary
  result := fun _ _ => none
  terminal_result := by simp [highSystem]
  terminal_no_step := by simp [highSystem]

private def highInitial : high.History :=
  .initial (state := .up 0) (graph := .up []) trivial

private def highWait : PermanentWait high.boundary highInitial where
  occurrence := (0 : Nat)
  pending := rfl
  permitted := trivial

private def highResponse : high.protocol.Response () := .up ()

example : Nonempty (PermanentWait high.boundary highInitial) := ⟨highWait⟩
example : Nonempty high.Complete := ⟨.waiting highInitial highWait⟩
example : Nonempty (high.MaximalContinuation highInitial) := ⟨.waiting .nil highWait⟩

private def lowSystem : RelationalSystem Unit where
  State := Nat
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ state _ _ next _ => next = state + 1
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

private def lowProtocol : WaitProtocol Unit where
  Response := fun _ => Unit
  Allowed := fun _ _ => True
  AllowsPermanentWait := fun _ => True

private def lowBoundary : lowSystem.WaitBoundary lowProtocol where
  Occurrence := Nat
  request := fun _ => ()
  Pending := fun history occurrence => history.state = occurrence
  External := fun _ _ => True
  Reply := fun _ _ _ => True
  reply_unique := by intro _ _ _ _ _ _; rfl
  nonterminal := by simp [lowSystem]
  step_external := by intros; trivial
  step_pending_or_reply := by intros; right; exact ⟨(), trivial, trivial⟩
  reply_allowed := by intros; trivial
  reply_ends := by
    intro history occurrence pending response choice event next nextGraph step reply later
    change next = occurrence at later
    have step' : (show Nat from next) = (show Nat from history.state) + 1 := by
      simpa only [lowSystem] using step
    have pending' : (show Nat from history.state) = occurrence := pending
    have impossible : occurrence = occurrence + 1 :=
      later.symm.trans (step'.trans (congrArg (· + 1) pending'))
    omega
  reply_path := by
    intro history occurrence pending response allowed
    exact ⟨history.state, history.graph, .nil, by intros; contradiction, pending, (), (),
      Nat.succ (show Nat from history.state), history.graph, trivial, by
        simp only [lowSystem]⟩

private def low : BehaviorModel Empty where
  Event := Unit
  Observation := Unit
  observationProjection := { project := fun _ => [] }
  Request := Unit
  system := lowSystem
  protocol := lowProtocol
  boundary := lowBoundary
  result := fun _ _ => none
  terminal_result := by simp [lowSystem]
  terminal_no_step := by simp [lowSystem]

private def exact : WaitTranslation high low where
  request := id
  response := fun _ _ => ()
  allowed := by intro _ _ _; trivial
  responseCoverage := by intro _ _ _; exact ⟨highResponse, trivial, rfl⟩
  permanent := by intro _; constructor <;> intro _ <;> trivial

/-- These aliases are interface-only checks: they do not construct a simulation
or claim behavior correspondence or implementation conformance. -/
private abbrev CorrespondenceAcrossUniverses :=
  BehaviorCorrespondence high low (fun _ => ()) exact
private abbrev ConformanceAcrossUniverses :=
  ImplementationConformance high low (fun _ => ())

private def correspondenceProjection (candidate : CorrespondenceAcrossUniverses) :
    BehaviorCorrespondence high low (fun _ => ()) exact := candidate
private def conformanceProjection (candidate : ConformanceAcrossUniverses) :
    ImplementationConformance high low (fun _ => ()) := candidate

end Grass.Tests.Semantics.BehaviorUniverses
