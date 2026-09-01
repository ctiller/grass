import Grass.Process
import Grass.Std.Process.Graphics
import Spikes.«5_Spinning_Cube».Spec

namespace Grass.Spikes.SpinningCube

inductive CubeRole
  | input
  | sceneAnimator
  | surfacePresenter
  | termination

def cubeProtocol : AbstractSpecificationProcessNetwork resources :=
  Graphics.interactivePresentationProtocol
    (roles := CubeRole)
    (resources := resources)
    (scene := scene)
    (accepts := CubeObservation.Accepts)

def cubeProcessPresentation : ProcessPresentation spec where
  network := cubeProtocol
  denotationExact := Graphics.interactivePresentationDenotesSceneContract
  requirementsExact := Graphics.interactivePresentationRequirementsExact

structure DesiredCubeView where
  extent : Nat × Nat
  sampledAt : MonotonicInstant
  angle : Angle

inductive FrameOpportunity
  | available (now : MonotonicInstant)

inductive CubePhase
  | running
  | stopping (outcome : CubeOutcome)
  | finished (outcome : CubeOutcome)

structure PendingCubeDemand where
  view : DesiredCubeView

structure CubeState where
  phase : CubePhase
  extent : Nat × Nat
  lastOpportunity : Option MonotonicInstant
  nextAngle : Angle
  pending : Multiset PendingCubeDemand

inductive FrameCommitResult (view : DesiredCubeView)
  | committed (frame : CubeFrame)
      (matches : FrameMatchesDesired scene view frame)
  | coalesced
  | failed (outcome : CubeOutcome) (notSuccess : outcome ≠ .userExit)

inductive FinishResult (outcome : CubeOutcome)
  | stopped

inductive CubeDemand
  | commitFrame (view : DesiredCubeView)
  | finish (outcome : CubeOutcome)

def CubeResult : CubeDemand → Type
  | .commitFrame view => FrameCommitResult view
  | .finish outcome => FinishResult outcome

def cubeApplication : ProcessSpec where
  Request := Unit
  State := CubeState
  TerminalResult := CubeOutcome
  ExternalEvent := CubeInput ⊕ FrameOpportunity
  Demand := CubeDemand
  Result := CubeResult
  Observation := CubeObservation
  Initial := CubeState.InitialWithDemands scene
  Terminal := CubeState.Terminal
  Step := CubeState.Step scene
  view := some { View := DesiredCubeView, render := CubeState.render scene }

theorem cubeApplicationCorrect : ProcessCorrect cubeApplication where
  Invariant := CubeState.Invariant scene
  initial := cube_initial_invariant
  initialDemands := cube_initial_demands_are_well_formed
  preserved := cube_step_preserves
  terminal := cube_terminal_accepts
  terminalNoStep := cube_terminal_has_no_step
  viewAccepts := cube_render_depicts_scene
  observationsAccept := cube_observations_accept
  demandsWellFormed := cube_demands_are_well_formed
  progress := cube_reactive_progress

inductive CubeProcessKind
  | application
  | windowInput
  | frameOpportunity
  | graphics
  | terminal
  | acquire (frame : DemandId)
  | submission (frame : DemandId)
  | presentation (frame : DemandId)
  | apiCall (call : CubeProviderCall)

inductive CubeSharedRegion
  | selectedProfile

inductive CubeProtocolKey
  | application
  | windowInput
  | frameOpportunity
  | graphics
  | terminal
  | acquire
  | submission
  | presentation
  | api (call : CubeProviderCall)

def cubeProtocols : ProtocolRegistry where
  Key := CubeProtocolKey
  protocol
    | .application => cubeApplication
    | .windowInput => win32WindowInputProtocol
    | .frameOpportunity => monotonicFrameOpportunityProtocol
    | .graphics => vulkanGraphicsProtocol
    | .terminal => win32TerminalProtocol
    | .acquire => vulkanAcquireProtocol
    | .submission => vulkanSubmissionProtocol
    | .presentation => vulkanPresentationProtocol
    | .api call => CubeProviderCall.protocol call

def processPlan : ProcessPlan cubeProtocols spec.driverBoundary where
  ProcessKind := CubeProcessKind
  SharedRegion := CubeSharedRegion
  SharedState := CubeSharedState
  protocolKey
    | .application => .application
    | .windowInput => .windowInput
    | .frameOpportunity => .frameOpportunity
    | .graphics => .graphics
    | .terminal => .terminal
    | .acquire _ => .acquire
    | .submission _ => .submission
    | .presentation _ => .presentation
    | .apiCall call => .api call
  root := .application
  rootBoundary := cube_root_exposes_boundary
  maySpawn := cubeMaySpawn
  sharedAccess := cubeSharedAccess
  population := cubePopulation
  ChannelKind := CubeChannelKind
  endpoints := CubeChannelEndpoints
  channel := CubeChannelContracts
  boundaryProjection := CubeBoundaryProjection
  spawn := CubeSpawnAuthority
  cancellation := CubeCancellationLaw
  supervision := CubeSupervisionLaw

theorem processPlanRealizes : ProcessPlanRealizes spec processPlan where
  processProofs := by
    intro kind
    cases kind with
    | application => exact cubeApplicationCorrect
    | windowInput => exact Std.Win32.windowInput_correct
    | frameOpportunity => exact Std.Process.monotonicFrameOpportunity_correct
    | graphics => exact Std.Vulkan.graphicsCoordinator_correct
    | terminal => exact Std.Win32.terminal_correct
    | acquire _ => exact Std.Vulkan.acquire_correct
    | submission _ => exact Std.Vulkan.submission_correct
    | presentation _ => exact Std.Vulkan.presentation_correct
    | apiCall call => exact CubeProviderCall.correct call
  composition := cube_channels_ownership_and_progress_compose
  adequate := cube_network_adequate
  simulation := cube_network_simulation
  demandMultiplicity := cube_occurrences_erase_exactly
  childBindings := cube_child_demand_bindings
  demands := cube_independent_safety_liveness_and_obligation_demands
  resources := cube_resource_axis_realization

theorem cubeResourceBound :
    EveryExecutionUsesAtMost
      ProcessScope.root
      CubeResourceMetric.product
      CubeResourceBudget.singleFrameInFlight :=
  processPlanRealizes.resources.rootBound

end Grass.Spikes.SpinningCube
