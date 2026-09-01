import Grass.Process
import Grass.Process.Blend
import Grass.Platform.Win10.Vulkan13
import Grass.Std.Graphics.Cube
import Grass.Std.Process.Graphics
import Spikes.«5_Spinning_Cube».Spec

namespace Grass.Spikes.SpinningCube

def projection : TargetProjection spec .win10X64Vulkan13Spirv15 :=
  TargetProjection.win10VulkanInteractive
    (clock := .queryPerformanceCounter)
    (userExitStatus := 0)
    (failureStatus := 1)

def vertexContract : ComponentContract :=
  Graphics.vertexProjectionContract scene

def fragmentContract : ComponentContract :=
  Graphics.fragmentColorContract scene

def vertexModel : ImplementationModel :=
  Graphics.cubeVertexModel scene

def fragmentModel : ImplementationModel :=
  Graphics.cubeFragmentModel scene

theorem vertexModelCorrect :
    ImplementationRealizesContract vertexModel vertexContract :=
  Graphics.cubeVertexModelCorrect scene

theorem fragmentModelCorrect :
    ImplementationRealizesContract fragmentModel fragmentContract :=
  Graphics.cubeFragmentModelCorrect scene

def rotationRepresentation : FloatingRotationRelation :=
  FloatingRotationRelation.ieee754
    (timeBase := .absoluteFromEpoch)
    (accumulator := .binary64)
    (shaderInput := .binary32)
    (reduction := .towardNegativeInfinityModuloTau)

theorem rotationRepresentationCorrect :
    FloatingRotationRelation.Refines
      rotationRepresentation rotationAccuracy scene.angularVelocity :=
  IEEE754.absoluteEpochBinary64_binary32Input_elapsedRotation
    rotationAccuracy scene.angularVelocity

def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64Vulkan13Spirv15 projection

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

def cubeProtocolResourceView : CubeRole -> RequiredResourceView resources :=
  Graphics.interactivePresentationResourceView

theorem cubeProtocolResourceRestrictionExact :
    forall schema,
      (cubeProtocol.protocol schema).resourceSemantics.restrict
          (cubeProtocolResourceView schema) =
        spec.resourceSemantics.restrict (cubeProtocolResourceView schema) :=
  Graphics.interactivePresentationResourceRestrictionExact

theorem cubeProtocolResourceViewsCoverRoot :
    ExactUnionOfRequiredResourceViews cubeProtocolResourceView
      spec.resourceSemantics.requiredAxes :=
  Graphics.interactivePresentationResourceViewsCoverRoot

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

theorem cubeApplicationProductive :
    ProcessSatisfiesProgress cubeApplication frameProductivity :=
  cube_frame_productivity

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
  progress := cube_progress_all cube_reactive_progress cubeApplicationProductive

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

def shapedSpec : StagedProcessPresentation spec :=
  StagedProcessPresentation.ofNetwork spec cubeProtocol
    cubeProtocolResourceView
    cubeProtocolResourceRestrictionExact
    cubeProtocolResourceViewsCoverRoot
    cubeProcessPresentation.denotationExact
    cubeProcessPresentation.requirementsExact

def inputSubsystem : SubsystemRealization shapedSpec .input :=
  SubsystemRealization.fromIndependentPlanScope
    processPlan (CubeProcessScope.input processPlan)
    cube_input_scope_correct
    cube_input_boundary_exact

def animationSubsystem : SubsystemRealization shapedSpec .sceneAnimator :=
  SubsystemRealization.fromIndependentPlanScope
    processPlan (CubeProcessScope.animation processPlan)
    cube_animation_scope_correct
    cube_animation_boundary_exact

def graphicsSubsystem : SubsystemRealization shapedSpec .surfacePresenter :=
  SubsystemRealization.fromIndependentPlanScope
    processPlan (CubeProcessScope.graphics processPlan)
    cube_graphics_scope_correct
    cube_graphics_boundary_exact

def terminationSubsystem : SubsystemRealization shapedSpec .termination :=
  SubsystemRealization.fromIndependentPlanScope
    processPlan (CubeProcessScope.termination processPlan)
    cube_termination_scope_correct
    cube_termination_boundary_exact

def completeGraph : BlendedProcessGraph shapedSpec where
  nodes
    | .input => .realized inputSubsystem
    | .sceneAnimator => .realized animationSubsystem
    | .surfacePresenter => .realized graphicsSubsystem
    | .termination => .realized terminationSubsystem
  composition := cube_all_subsystem_boundaries_compose
  requirements := cube_all_requirement_union

def completePartial : PartialProcessRealization shapedSpec completeGraph :=
  ProcessRealization.blend completeGraph

def completeClosedBlend : ClosedBlend completePartial
    cube_every_schema_realized_parametrically
    cube_portable_requirements_resources_obligations_coherent :=
  completePartial.close
    cube_every_schema_realized_parametrically
    cube_portable_requirements_resources_obligations_coherent

def stagedProcessRealization : ProcessRealization spec :=
  completeClosedBlend.realization

theorem stagedPlanIsExact :
    stagedProcessRealization.plan = processPlan :=
  cube_closed_blend_elaborates_to_exact_plan

theorem processPlanRealizes : ProcessPlanRealizes spec processPlan :=
  stagedProcessRealization.transportPlan stagedPlanIsExact

theorem cubeResourceBound :
    EveryExecutionUsesAtMost
      ProcessScope.root
      CubeResourceMetric.product
      CubeResourceBudget.singleFrameInFlight :=
  processPlanRealizes.resources.rootBound

theorem unresolvedDescendantRejected :
    ¬ FrontierComplete cube_graphics_with_abstract_child :=
  cube_abstract_child_is_reachable

theorem conflictingProvidersRejected :
    ¬ RequirementDeltasCompatible cube_vulkan_delta cube_metal_delta :=
  cube_vulkan_metal_conflict

end Grass.Spikes.SpinningCube
