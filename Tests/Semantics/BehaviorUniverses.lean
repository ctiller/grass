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
private abbrev HighState := ULift.{1} Unit
private abbrev HighGraph := ULift.{1} Raw.Graph

private def highSystem : RelationalSystem.{1} HighEvent where
  State := HighState
  Choice := Raw.Choice
  Graph := HighGraph
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
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
  Occurrence := Unit
  request := id
  Pending := fun _ _ => True
  Reply := fun _ _ _ => True
  reply_unique := by
    intro _ first second _ _ _
    cases first
    cases second
    rfl
  nonterminal := by simp [highSystem]
  step_reply := by
    intro _ _ _ _ _ _ _ _
    exact ⟨.up (), trivial, trivial⟩
  reply_step := by
    intro history _ _ response _
    exact ⟨.cpu (.interruption 0), .up { memory := [], boundaries := [], kind := .internal },
      .up (), history.graph, trivial, trivial⟩

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
  .initial (state := .up ()) (graph := .up []) trivial

private def highWait : PermanentWait high.boundary highInitial where
  occurrence := ()
  pending := trivial
  permitted := trivial

private def highResponse : high.protocol.Response () := .up ()

example : Nonempty (PermanentWait high.boundary highInitial) := ⟨highWait⟩
example : Nonempty high.Complete := ⟨.waiting highInitial highWait⟩
example : Nonempty (high.MaximalContinuation highInitial) := ⟨.waiting .nil highWait⟩

private def lowSystem : RelationalSystem Unit where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
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
  Occurrence := Unit
  request := id
  Pending := fun _ _ => True
  Reply := fun _ _ _ => True
  reply_unique := by intro _ _ _ _ _ _; rfl
  nonterminal := by simp [lowSystem]
  step_reply := by intro _ _ _ _ _ _ _ _; exact ⟨(), trivial, trivial⟩
  reply_step := by intro _ _ _ _ _; exact ⟨(), (), (), (), trivial, trivial⟩

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

private def directed : DirectedWaitTranslation high low where
  request := id
  response := fun _ _ => ()
  allowed := by intro _ _ _; trivial
  permanent := by intro _ _; trivial

private def exact : WaitTranslation high low where
  request := id
  response := fun _ _ => ()
  allowed := by intro _ _ _; trivial
  responseCoverage := by intro _ _ _; exact ⟨highResponse, trivial, rfl⟩
  permanent := by intro _; constructor <;> intro _ <;> trivial

/-- These aliases are interface-only checks: they do not construct a simulation
or claim behavior correspondence or implementation conformance. -/
private abbrev DirectedAcrossUniverses := DirectedWaitTranslation high low
private abbrev CorrespondenceAcrossUniverses :=
  BehaviorCorrespondence high low (fun _ => ()) exact
private abbrev ConformanceAcrossUniverses :=
  ImplementationConformance high low (fun _ => ()) directed

private def directedProjection (translation : DirectedAcrossUniverses) :
    DirectedWaitTranslation high low := translation
private def correspondenceProjection (candidate : CorrespondenceAcrossUniverses) :
    BehaviorCorrespondence high low (fun _ => ()) exact := candidate
private def conformanceProjection (candidate : ConformanceAcrossUniverses) :
    ImplementationConformance high low (fun _ => ()) directed := candidate

end Grass.Tests.Semantics.BehaviorUniverses
