# Spike 5: a spinning cube across x86-64, Vulkan, and SPIR-V

Status: design artifact for adversarial review; intentionally not compilable.

Authoring view: agents maintain `Spec.lean`, `Process.lean`, `Layout.lean`,
`Macros.lean`, `Assembly.lean`, and `Program.lean`. The exact snapshot is at the
end of this document. Source closure, cross-ISA manifests, and artifact bundles
are generated inspection views.

| Proof-economics quantity | Current evidence |
| --- | --- |
| Authored specification | 1 module; 97 physical / 77 nonblank lines |
| Authored realization | 5 modules; 1666 physical / 1553 nonblank lines |
| Generated expansion/certificates | not generated |
| Clean/incremental checking | not measured |

Future generation, proof, artifact, mutation, and locality evidence follows the
shared [implementation ratchet](IMPLEMENTATION_RATCHET.md), including the
Spike 5 first-failure fixtures; none is claimed as present here.

The five realization modules currently separate process proofs, ABI/layout
selection, host constructors, host plus shader assembly, and the closing form.
The displayed layout and cross-ISA selections are application construction
inputs; generated offsets, manifests, source closure, and object aggregation do
not receive authored modules. Physical sharding follows the `.olean` design and
may split the combined assembly module when measurement warrants it.

This spike proposes the complete proof shape before its libraries exist. It is
not permission to build the graphics framework yet. The resource-parameterized
portable specification function is the precious semantic artifact. The selected
resource model is reviewed configuration. The root application
process is their platform-independent proof model. The exact
process topology, coherent platform plan, authored x86-64 CFG, and authored
SPIR-V modules are reviewed and replaceable construction inputs. Certificates,
layouts, import tables, shader words, and PE bytes are derived.

## 1. The application proof we want to read

<!-- grass-block: proof-sketch id=spike5-block-01 -->
```lean
namespace Grass.Spike5

/-! A unit cube, perspective projection, rotation as a function of portable
monotonic elapsed time, resize, and user-requested termination are semantic.
Graphics APIs, clock APIs, refresh rate, and physical scheduling are not. -/
def geometry : WireGeometry := WireGeometry.unitCube

def vertexColors : VertexColoring geometry :=
  VertexColoring.byVertex #[.red, .green, .blue, .yellow,
    .cyan, .magenta, .white, .black]

def angularVelocity : AngularVelocity := .radiansPerSecond (3 / 5)

def scene : InteractiveScene :=
  Scene.spinningWireGeometry geometry vertexColors angularVelocity

structure CubeFrame where
  extent : Nat × Nat
  sampledAt : MonotonicInstant
  angle : Angle
  image : AbstractImage

def rotationAccuracy : ElapsedRotationAccuracy :=
  ElapsedRotationAccuracy.explicit
    (maxAngleError := .radians (1 / 1024))
    (maxSampleTimeError := .milliseconds 1)

def frameProductivity : ProgressFragment :=
  ProgressFragment.conditionalProductivity
    (enabled := [.running, .visible, .nonzeroExtent, .noExitRequested])
    (assumptions := [.frameOpportunitiesContinue, .schedulerFair,
      .platformResponsive, .gpuResponsive])
    (opportunity := .frameOpportunity)
    (eventually := [.frameObservation, .terminalOutcome])

inductive CubeInput
  | close | escapeDown | resize (width height : Nat) | irrelevant

inductive CubeOutcome
  | userExit | initializationFailure | graphicsFailure | surfaceLost

structure CubeObservation where
  inputs : Stream CubeInput
  frames : Stream CubeFrame
  outcome : Option CubeOutcome

def CubeObservation.Accepts (o : CubeObservation) : Prop :=
  FramesApproximateElapsedRotation
      scene.angularVelocity rotationAccuracy o.frames ∧
  NondecreasingFrameSampleTimes o.frames ∧
  (∀ frame ∈ o.frames,
    RasterizesProjectedWireScene scene frame.extent frame.angle frame.image) ∧
  ResizeAffectsProjectionOnly o.inputs o.frames ∧
  UserExitIffRequestedForConformingRuns o.inputs o.outcome ∧
  FailureNeverNormalizesToUserSuccess o.outcome

def resources : GraphicsResourceModel :=
  GraphicsResourceModel.longLivedApplication
    |>.withNoUnboundedGrassOwnedGrowth
    |>.withTerminalDisposition .closeAllOwnedGraphicsObjects

def sceneFragment : SceneSpec := Graphics.sceneSpec scene

def cubeTraceFragment {R : Type} [ResourceModel R]
    (resources : R) : TraceSpec resources :=
  Graphics.interactiveTraceSpec CubeInput CubeObservation CubeObservation.Accepts

def cubeSuite {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : SpecificationSuite resources :=
  Graphics.interactiveSceneSuite
    resources sceneFragment (cubeTraceFragment resources) rotationAccuracy

def cubeSpec {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (cubeSuite resources)
    |>.acceptInput [.close, .escapeDown, .resize, .irrelevant]
    |>.withFailures .terminateWithoutFalseSuccess
    |>.withProgress (.all #[
      .reactiveUntilUserExit frontiers :=
        [.externalInput, .frameOpportunity, .frameObservation, .terminalOutcome],
      frameProductivity])

theorem cubeSpecCorrect {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : MeetsAllSpecificationTheorems (cubeSpec resources) :=
  Graphics.interactiveSceneSuiteCaptureCorrect
    resources scene CubeObservation.Accepts rotationAccuracy

def spec : SpecProcess resources := cubeSpec resources

inductive CubeRole
  | input | sceneAnimator | surfacePresenter | termination

def cubeProtocol : AbstractSpecificationProcessNetwork resources :=
  Graphics.interactivePresentationProtocol
    (roles := CubeRole) (resources := resources)
    (scene := scene) (accepts := CubeObservation.Accepts)

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

inductive FrameCommitResult (scene : InteractiveScene)
    (view : DesiredCubeView)
  | committed (frame : CubeFrame)
      (matches : FrameMatchesDesired scene view frame)
  | coalesced
  | failed (outcome : CubeOutcome) (notSuccess : outcome ≠ .userExit)

inductive FinishResult (outcome : CubeOutcome)
  | stopped

inductive CubeDemand
  | commitFrame (view : DesiredCubeView)
  | finish (outcome : CubeOutcome)

def CubeResult : CubeDemand -> Type
  | .commitFrame view => FrameCommitResult scene view
  | .finish outcome => FinishResult outcome

/-! This is the replaceable portable proof model. It contains no host message, swapchain,
queue, callback, or shader convention. -/
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
  view := some { View := DesiredCubeView
                 render := CubeState.render scene }

/-! Reviewed and replaceable: this is one process weave, not part of `spec`. -/
def processPlan := cubeWin32VulkanProcessPlan

theorem processPlanRealizes : ProcessPlanRealizes spec processPlan := by
  exact cubeWin32VulkanDriverCorrect

/-! One value fixes every provider dictionary and compatibility proof required
by the selected process plan. -/
def projection : TargetProjection spec .win10X64Vulkan13Spirv15 :=
  TargetProjection.win10VulkanInteractive
    (clock := .queryPerformanceCounter)
    (userExitStatus := 0)
    (failureStatus := 1)

def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64Vulkan13Spirv15 projection

def shaders : ShaderSet plan :=
  { vertex := cubeVertex
    fragment := cubeFragment }

def source : MachineSource plan :=
  { host := cubeHost
    devices := shaders }

def sourceConnections : HeterogeneousSourceConnections plan source :=
  machine_connections {
    callback `wndproc =>
      Win32.windowStatePointer
        (installAt := .wmNcCreate)
        (clearAt := .wmNcDestroy)
    shader `vertexShader =>
      Spirv.module cubeVertex
        (entry := `main)
        (staticRange := `cubeVertexBytes)
        (createCall := `vkCreateShaderModule)
        (codeSize := `cubeVertexBytes.size)
        (codePointer := `cubeVertexBytes.address)
        (returnedHandle := `vertModule)
        (pipelineStage := (`shaderStages, 0, VERTEX_BIT))
        (entryName := `mainName)
    shader `fragmentShader =>
      Spirv.module cubeFragment
        (entry := `main)
        (staticRange := `cubeFragmentBytes)
        (createCall := `vkCreateShaderModule)
        (codeSize := `cubeFragmentBytes.size)
        (codePointer := `cubeFragmentBytes.address)
        (returnedHandle := `fragModule)
        (pipelineStage := (`shaderStages, 1, FRAGMENT_BIT))
        (entryName := `mainName)
    pushConstant `rotation => rotationRepresentation
  }

theorem sourceConnectionsCorrect :
    HeterogeneousSourceConnections.Valid sourceConnections := by
  verify_machine_connections
    using_rotation rotationRepresentationCorrect

def cubeVerified : VerifiedProgram spec := by
  verify_assembly plan
    using_process stagedProcessRealization
    using_models vertexModelCorrect fragmentModelCorrect
    using_machine_proofs hostImplementsDriver vertexCorrect fragmentCorrect
    using_connections sourceConnectionsCorrect
    with source

def bytes : ByteArray := emitProgram cubeVerified

end Grass.Spike5
```

The four root progress frontiers are semantic boundary classes: accepted
external input, an environment-provided opportunity to produce a frame, an
observable accepted frame, and an observable terminal outcome. They do not name
the application's command/result loop, Vulkan calls, queue submission, or an
internal commit stage. Those belong to the replaceable process presentation and
its driver proof.

`sampledAt` names the host clock sample used to construct the frame; it is not
an unobservable physical display time. `NondecreasingFrameSampleTimes` admits
two opportunities in one clock tick. In that case the elapsed interval is zero
and `FramesApproximateElapsedRotation` requires the same represented angle.
The portable specification names a representation-independent angular accuracy,
not a floating format. The realization's separate `rotationRepresentation`
compares each binary32 shader input with ideal angular velocity times elapsed
portable time modulo tau. Its bound is derived from the actual binary64
epoch subtraction, division, multiplication and reduction, followed by
binary64-to-binary32 conversion; it is not equality between a floating value
and an ideal real angle. The standard library must prove that per-operation
IEEE-754 bound refines `rotationAccuracy` over every admitted clock value before
the representation is available to this spike.

Geometry, vertex colors, and angular velocity are ground precious values, so a
change such as “spin twice as fast” is visibly a `Spec.lean` edit. The library
supplies scene vocabulary and rasterization relations, not this cube's product
content. `CubeFrame` is observation data rather than a proof-carrying value;
the acceptance relation separately demands that every observed frame depicts
the specified geometry and vertex colors at the specified angle.

No precious declaration contains a process count, channel buffer, message-loop
convention, Vulkan result, matrix byte layout, shader language, fixed frame
rate, exit code, or PE detail. `processPlan` chooses those facts and
`processPlanRealizes` proves that the choice implements the root protocol. The
platform plan supplies a Win32 terminal policy: clean user exit is status zero;
any unrecoverable initialization/runtime failure is nonzero. Physical frames
and input events are filtered to the observations needed by `spec`.

## 2. Portable observation and reactive law

The `CubeObservation.Accepts` declaration above does not demand pixel identity
across GPUs. The Vulkan realization proves
that the shader/pipeline/rasterization model refines
`RasterizesProjectedWireScene` for the complete scene, including colors;
implementation-defined precision is represented by a reviewed numeric error
envelope, not hidden under equality. Occluded or minimized windows may present
no frames. Individual frame opportunities may be coalesced. They may not be
discarded forever while the application is running, visible, has nonzero extent,
has no exit request, and continuing frame opportunities, scheduler fairness,
platform responsiveness, and GPU responsiveness all hold: under those premises
the trace eventually contains an accepted frame or a declared terminal outcome.
This is conditional productivity, not a fixed cadence or frame-rate promise. A
close/Escape request forbids new submissions after the currently submitted frame
is retired.

Every finite conforming prefix is safe. The host performs finite work between
frontiers. An infinite execution with no user exit is an intended reactive run.
If a compatible branching strategy eventually supplies close/Escape and every
already-issued Win32/Vulkan/GPU frontier settles, cleanup and termination are
finite. A permanently pending driver call is safe but does not satisfy the
responsive-strategy premise.

The portable proof model's `CubeState.Step` relation has only these application rules:

- irrelevant input stutters and emits no demand;
- resize changes the desired extent but does not itself commit a frame;
- a frame opportunity carrying monotonic instant `now` while running may append
  `commitFrame (render (advanceByElapsed state now))` with a fresh identity and
  the ordering dependency needed to preserve elapsed-time rotation; the portable
  ledger imposes no fixed in-flight bound;
- a correlated committed response appends exactly that accepted frame and moves
  to a permitted later angle; a coalesced response emits no observation;
- close or Escape moves to stopping and demands cancellation of every
  uncommitted frame,
  and permits `finish .userExit` only after already committed submissions are
  retired; and
- a correlated failure moves to the matching failure outcome and can never emit
  user success.

The application proof is consequently the small reusable package we want:

<!-- grass-block: interface id=spike5-block-02 -->
```lean
theorem cubeApplicationCorrect : ProcessCorrect cubeApplication := by
  constructor
  · exact cube_initial_invariant
  · exact cube_initial_demands_are_well_formed
  · intro s event s' demands emitted hs hstep
    exact cube_step_preserves hs hstep
  · exact cube_terminal_accepts
  · exact cube_terminal_has_no_step
  · exact cube_render_depicts_scene
  · exact cube_observations_accept
  · exact cube_demands_are_well_formed
  · exact cube_reactive_progress
```

No theorem here mentions a window handle, image index, semaphore, command
buffer, queue, or machine register.

## 3. Reviewed process plan and driver proof

The following topology is complete for this realization and deliberately not
precious. A different implementation may merge the three graphics children,
use several frames in flight, or replace Win32/Vulkan while proving the same
`ProcessPlanRealizes spec` boundary.

The child protocol declarations are stable standard-library specifications and
must themselves be proved correctly. Selecting these protocols, their instance
population, and this channel weave is the replaceable construction input; it is
not an extension of the application's precious observation contract.

`CubeProviderCall` is the finite nominal sum of the Win32/global-Vulkan imports
and resolved instance/device commands listed exactly in section 7.6. Its
registry theorem rejects missing or extra call identities. Every constructor
carries the standard dependent result protocol, citation, and correctness
witness; it is not an open "external call succeeds" escape hatch.

<!-- grass-block: proof-sketch id=spike5-block-03 -->
```lean
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
  | selectedProfile -- immutable after initialization

inductive CubeProtocolKey
  | application | windowInput | frameOpportunity | graphics | terminal
  | acquire | submission | presentation
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

def cubeWin32VulkanProcessPlan :
    ProcessPlan cubeProtocols spec.driverBoundary where
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
```

`cubePopulation` requires exactly one application, window-input source,
frame-opportunity source, graphics coordinator, and terminal child. Acquire, submission,
presentation, and individual Win32/Vulkan API-call children are generative and
carry the initiating demand occurrence. With one frame in flight, at most one of
each frame child is live and every live child is reachable from its unique root
demand. These are implementation facts, not promises of `spec`.

### 3.1 Child protocols

The standard Win32 window child owns class/`HWND` lifetime and callback loans.
Its events are close, Escape, resize, irrelevant message, minimized/restored,
and provider failure. `PeekMessageW` removal order and `DispatchMessageW`
reentrancy refine its ordered channel. Resize may coalesce; close/Escape may
not be dropped. Destruction returns the surface-lifetime loan before class
unregistration. The application sees only `CubeInput`, never `MSG`, `WPARAM`,
or `LPARAM`.

The frame-opportunity child has `idle`, `offered id`, and `suppressed` states.
It may offer only while the window is non-minimized, shutdown has not begun,
and the graphics coordinator can accept a frame. Offers may be coalesced. It
does not promise an opportunity cadence and has no commit authority. Each offer
carries a portable monotonic instant; the selected Win32 child refines
`QueryPerformanceCounter` ticks and frequency to that instant and proves
non-regression for conforming results.

The graphics coordinator reconciles `DesiredCubeView` into the selected
Vulkan resource graph. Each frame demand expands into identity-correlated
children with these terminal projections:

<!-- grass-block: interface id=spike5-block-04 -->
```lean
Acquire(frame, generation)
  : acquired(image, imageLoan) | recreate | cancelled | deviceLost | surfaceLost
Submission(frame, imageLoan)
  : submitted(submission, inFlightLoan) | cancelledBeforeSubmit
  | deviceLost | invalidEnvironment
Presentation(frame, inFlightLoan)
  : committed(CubeFrame) | recreateAfterRetire | deviceLost | surfaceLost
```

Acquire owns no image before a successful dependent result. Submission consumes
the exact acquired-image loan and cannot be cancelled after queue commit;
cancellation then means "stop issuing work and drain this occurrence."
Presentation is the sole child allowed to append a frame observation, and only
after the provider's presentation commit law. Out-of-date/suboptimal responses
request recreation without fabricating a frame. Device loss applies the cited
loss disposition to every affected child and can only project to
`.graphicsFailure`; surface loss projects to `.surfaceLost`.

The terminal child accepts `finish outcome` only after the graphics and window
children have returned or discharged every non-adoptable obligation. Its
dependent response records the selected nonzero failure status or zero user-exit
status, while `spec` observes only `CubeOutcome`. `ExitProcess` is its Win32
realization, not a property baked into the root process.

Every concrete `win_call` and `vk_call` below is itself a standard API child
process occurrence. Synchronous syntax suspends the owning process until the
child's terminal projection; it does not turn environmental entropy into a pure
function. Dependent counts, output initialization, pending behavior,
interruption, callback reentrancy, faults, and provider violations remain in
the child protocol.

### 3.2 State ownership and channels

There is no mutable shared application state in this plan. The application
alone owns `CubeState`; the window child owns its message state and window
ledger; the graphics coordinator owns instance/device/surface/swapchain and
long-lived synchronization ledgers. Per-frame children receive affine loans
over the exact image, semaphore, fence, command buffer, and swapchain
generation, then return, transfer, or discharge them at their typed terminal
edge. `selectedProfile` is immutable read-shared configuration.

Channels are exact Hoare-style `ChannelContract`s. They carry values,
identities, and obligations rather than aliases: every affine Vulkan loan and
demand occurrence resides in stable `Escrow` after send. Its affine resolve
token permits at most one receive or cited cancellation/device-loss disposition;
an unrestricted pending execution may retain it forever.

<!-- grass-block: interface id=spike5-block-05 -->
```text
windowInput      -> application : ordered CubeInput; resize coalescible
frameOpportunity -> application : coalescible FrameOpportunity
application      -> graphics    : commitFrame with fresh DemandOccurrence
graphics         -> application : dependent frame result with same occurrence
application      -> terminal    : finish after the obligation barrier
terminal         -> application : dependent finish result with same occurrence
graphics         -> acquire     : desired view + generation loans
acquire          -> submission  : exact acquired-image loan
submission       -> presentation: exact in-flight loan
presentation     -> graphics    : commit/recreate/failure + returned loans
```

Callback entry is an interleaving in the window child. GPU completion and
presentation are provider events in the appropriate frame child. No process
observes another process's local state by reading a shared Lean record.

### 3.3 The realization theorem

<!-- grass-block: proof-sketch id=spike5-block-06 -->
```lean
theorem cubeWin32VulkanDriverCorrect :
    ProcessPlanRealizes spec cubeWin32VulkanProcessPlan := by
  exact
    { processProofs := by
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
      resources := cube_resource_axis_realization }
```

### 2.2 Staged subsystem blend

The cube also supplies the architectural mutation fixture for orthogonal
lowering. `RoleSchema` is finite while any dynamic role instances are quantified
inside their subsystem certificate. The graphics-only value retains abstract
input, animation, and termination schemas and is therefore proof-bearing but
not emittable:

<!-- grass-block: interface id=spike5-block-07 -->
```lean
def shapedSpec : StagedProcessPresentation spec :=
  StagedProcessPresentation.ofNetwork spec cubeProtocol
    cubeProtocolResourceView
    cubeProtocolResourceRestrictionExact
    cubeProtocolResourceViewsCoverRoot
    cubeProcessPresentation.denotationExact
    cubeProcessPresentation.requirementsExact

def graphicsOnlyGraph : BlendedProcessGraph shapedSpec where
  nodes
    | .input => .abstract
    | .sceneAnimator => .abstract
    | .surfacePresenter => .realized graphicsSubsystem
    | .termination => .abstract
  composition := cube_graphics_only_boundaries_compose
  requirements := cube_graphics_only_requirement_union

def graphicsOnly : PartialProcessRealization shapedSpec graphicsOnlyGraph :=
  ProcessRealization.blend graphicsOnlyGraph

theorem graphicsOnlyNotEmittable :
    ¬ EmittableProcessRealization graphicsOnly :=
  PartialProcessRealization.notEmittable
    graphicsOnly cube_graphics_only_has_abstract_schemas
```

Input and graphics refinements are applied in both orders and prove graph
isomorphism because their exported boundaries and requirement deltas are
disjoint. The complete graph names all four exact portable subsystem
certificates; closure consumes that same indexed partial value, proves every
schema and every reachable descendant frontier closed, and returns the process
realization used below:

<!-- grass-block: interface id=spike5-block-08 -->
```lean
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
```

The staged-process library must separately carry negative fixtures rejecting an
abstract nested child, Vulkan/Metal provider conflict, changed occurrence
multiplicity, increased resource flux, and new silent divergence. Those are
library validation fixtures, not authored cube files. A general graphics /
storage / simulation commutation fixture likewise belongs with the blend
library: it pressure-tests staged lowering without adding disk I/O to this
cube's precious behavior or charging the application author another module.

The root is the only application-specific local process proof. The composition
witness is plan-specific: it owns swapchain generations, acquired-image loans,
submission/presentation races, device/surface loss, cancellation, clock-event
correlation, and reverse cleanup. The generic process library supplies the
induction skeleton and framing but does not discover those invariants.

The intended handwritten burden is `cubeApplicationCorrect`, the channel and
ownership facts unique to this weave, the non-vacuous population/choice coverage
instantiation, and the observation-filter simulation. Standard child, lifecycle,
strategy, and physical-representation templates are selected, not rederived. None of this replaces the
later local proofs for the authored x86 or SPIR-V instructions.

The displayed cube registry is a compact authoring presentation, not a
whole-engine module shape. Checked expansion emits separate opaque process
shards for the application, window/input host, graphics coordinator, and
generative frame family. Channel, ownership, cancellation, resource, progress,
and provider facts are facet-indexed and composed through a balanced certificate
DAG. Independently replacing the graphics shard with Vulkan or later lowering a
storage shard to IOCP preserves unrelated siblings, as required by
[PROCESS_SHARDING.md](PROCESS_SHARDING.md).

The reusable driver argument relates each logical process occurrence to an
exact CFG interval: `wndproc`/`pump_messages` implement the input child;
`event_loop` and the minimized gate implement frame opportunities;
`vkAcquireNextImageKHR` through `acquired` implements acquisition; command
recording through `vkQueueSubmit2` implements submission; and
`vkQueuePresentKHR` plus recreation/cleanup implements presentation and
cancellation disposition. The relation retains one namespaced choice oracle
across Win32, Vulkan, scheduling, and GPU execution. It proves finite internal
work to the next process frontier, response correlation, pure-render
discardability, no post-exit submission, exact commit filtering, and the
conditional productivity theorem: repeated enabled opportunities cannot stutter
forever when its explicit fairness and responsiveness premises hold.

`processPlanRealizes` does not claim that these labels or this topology are
semantic. It claims their projected traces satisfy `spec`; replacing the weave
requires this theorem again but does not edit the precious application.

## 4. Coherent platform and device selection

The plan fixes these nominal identities together:

<!-- grass-block: interface id=spike5-block-09 -->
```text
host ISA          common-x86-64 + Microsoft x64 ABI
host platform     Windows 10 Win32 desktop
graphics API      Vulkan 1.3
instance ext      VK_KHR_surface, VK_KHR_win32_surface
device ext        VK_KHR_swapchain
device features   dynamicRendering = VK_TRUE, synchronization2 = VK_TRUE
shader env        Vulkan 1.3 / SPIR-V 1.5 / Shader capability
artifact          PE32+ GUI subsystem, ASLR, NX-compatible
```

Selection proves one queue family supports both graphics and the created Win32
surface. It accepts only `VK_FORMAT_B8G8R8A8_UNORM` with
`VK_COLOR_SPACE_SRGB_NONLINEAR_KHR`, `VK_PRESENT_MODE_FIFO_KHR`, color-attachment
usage, composite alpha opaque, and a nonzero surface extent. FIFO is required,
not guessed from enumeration order. Unsupported machines fail initialization;
the portable spec does not promise universal GPU availability.

The only PE imports from `vulkan-1.dll` are `vkGetInstanceProcAddr` and
`vkGetDeviceProcAddr`. Every other Vulkan function pointer is obtained through
the appropriate resolver, checked non-null, given an exact nominal API identity,
and stored in a read-only-after-initialization dispatch table. Win32 imports are
derived from the literal operations below.

## 5. Resources, synchronization, and obligations

The ledger contains nominal, non-forgeable resources:

<!-- grass-block: interface id=spike5-block-10 -->
```lean
WindowClass -> HWND -> VkSurfaceKHR
VkInstance -> VkSurfaceKHR
VkPhysicalDevice(selection witness)
VkDevice -> VkQueue
VkSwapchainKHR -> Vec SwapImage
SwapImage -> VkImageView
VkDevice -> VkPipelineLayout -> VkPipeline
VkDevice -> VkCommandPool -> VkCommandBuffer
VkDevice -> imageAvailable semaphore
VkDevice -> renderFinished semaphore
VkDevice -> inFlight fence
```

Creation transfers a destroy obligation to the host ledger only on `VK_SUCCESS`
with a valid output. Failure retains every prior owner and creates no fictitious
handle. Destruction occurs in reverse dependency order. `HWND` destruction
precedes class unregistration but follows surface destruction. `VkInstance` is
last among Vulkan objects. Process termination may adopt process-private host
storage, but cannot adopt live Vulkan work or a live surface.

One frame is in flight. The loop transition is:

<!-- grass-block: interface id=spike5-block-11 -->
```text
FenceSignaled
  --vkWaitForFences--> FenceSignaled
  --vkResetFences--> FenceUnsignaled
  --vkAcquireNextImageKHR(imageAvailable)--> Acquired(imageIndex)
  --record command buffer--> Executable(imageIndex, Present->Color->Present)
  --vkQueueSubmit2(wait imageAvailable, signal renderFinished, fence)-->
       Submitted(imageIndex, fence)
  --vkQueuePresentKHR(wait renderFinished)--> PresentPending(imageIndex)
  --queue/semaphore/fence progress in provider execution-->
       ReleasedToPresentation(imageIndex) + FenceSignaled
```

The provider model accounts for the fact that presentation and fence completion
are distinct; recreation first executes `vkDeviceWaitIdle`, which proves no
command buffer, image view, or old swapchain image remains in use. An
out-of-date/suboptimal acquire or present marks recreation required. A zero
extent enters `minimized_wait` and performs only Win32 message waits until a
nonzero resize or exit. Device/surface loss enters terminal cleanup as permitted
by the Vulkan disposition profile; no invalid destroy is claimed after an
externally lost object.

## 6. Complete authored SPIR-V modules

The portable graphics mathematics is banked before either shader is authored:

<!-- grass-block: interface id=spike5-block-12 -->
```lean
def vertexContract : ComponentContract :=
  Graphics.vertexProjectionContract scene

def fragmentContract : ComponentContract :=
  Graphics.fragmentColorContract scene

def vertexModel : ImplementationModel := Graphics.cubeVertexModel scene
def fragmentModel : ImplementationModel := Graphics.cubeFragmentModel scene

theorem vertexModelCorrect :
    ImplementationRealizesContract vertexModel vertexContract

theorem fragmentModelCorrect :
    ImplementationRealizesContract fragmentModel fragmentContract

def rotationRepresentation : FloatingRotationRelation :=
  FloatingRotationRelation.ieee754
    (timeBase := .absoluteFromEpoch)
    (accumulator := .binary64)
    (shaderInput := .binary32)
    (reduction := .towardNegativeInfinityModuloTau)

theorem rotationRepresentationCorrect :
    FloatingRotationRelation.Refines
      rotationRepresentation rotationAccuracy scene.angularVelocity

theorem cubeVertex_refines_model :
    AssemblyRefinesImplementation
      vertexShaderScope VertexSpirvRepresentation vertexModel cubeVertex

theorem cubeFragment_refines_model :
    AssemblyRefinesImplementation
      fragmentShaderScope FragmentSpirvRepresentation fragmentModel cubeFragment
```

The pipeline/provider connection composes those component contracts with the
accepted numeric envelope and rasterization observation. A shader optimization
re-proves only its exact module-to-model adjacency; it does not reopen the cube
geometry or root process proof.

These are first-class `spirv_asm` values, not GLSL compiler output. Symbolic IDs
are Lean names; the writer assigns dense numeric IDs. The standard SPIR-V reader
and writer prove modeled round-trip, logical-layout validity, declared
capabilities, dominance/SSA, interface matching, and Vulkan-environment rules.
`spirv-val` differential validation is a probe, not proof.

The vertex shader synthesizes the 24 endpoints of the twelve cube edges from
constant arrays, rotates about the Y axis, applies aspect-correct perspective,
and exports a position-derived color. There is no vertex buffer, index buffer,
depth buffer, or descriptor set. The product is explicitly a wireframe cube;
the proof must not pass off depth-incorrect filled triangles as a solid cube.

<!-- grass-block: interface id=spike5-block-13 -->
```spirv
def cubeVertex : SpirvModule plan.shaderEnv := spirv_asm {
  OpCapability Shader
  %glsl = OpExtInstImport "GLSL.std.450"
  OpMemoryModel Logical GLSL450
  OpEntryPoint Vertex %main "main" %vertexIndex %positionOut %colorOut
    %push %positionsVar %indicesVar
  OpName %main "main"
  OpDecorate %vertexIndex BuiltIn VertexIndex
  OpDecorate %positionOut BuiltIn Position
  OpDecorate %colorOut Location 0
  OpMemberDecorate %Push 0 Offset 0
  OpMemberDecorate %Push 1 Offset 4
  OpDecorate %Push Block

  %void = OpTypeVoid
  %fn = OpTypeFunction %void
  %bool = OpTypeBool
  %int = OpTypeInt 32 1
  %uint = OpTypeInt 32 0
  %float = OpTypeFloat 32
  %i0=OpConstant %int 0  %i1=OpConstant %int 1
  %i2=OpConstant %int 2  %i3=OpConstant %int 3
  %i4=OpConstant %int 4  %i5=OpConstant %int 5
  %i6=OpConstant %int 6  %i7=OpConstant %int 7
  %u8=OpConstant %uint 8  %u24=OpConstant %uint 24
  %f0=OpConstant %float 0.0  %f1=OpConstant %float 1.0
  %fn1=OpConstant %float -1.0  %f2=OpConstant %float 2.0
  %f3=OpConstant %float 3.0  %f025=OpConstant %float 0.25
  %v3 = OpTypeVector %float 3
  %v4 = OpTypeVector %float 4
  %Push = OpTypeStruct %float %float
  %ptrPush = OpTypePointer PushConstant %Push
  %ptrPushF = OpTypePointer PushConstant %float
  %ptrInI = OpTypePointer Input %int
  %ptrOutV4 = OpTypePointer Output %v4
  %ptrOutV3 = OpTypePointer Output %v3
  %arrPos = OpTypeArray %v3 %u8
  %arrIdx = OpTypeArray %int %u24
  %ptrPrivatePos = OpTypePointer Private %arrPos
  %ptrPrivateIdx = OpTypePointer Private %arrIdx
  %ptrPrivateV3 = OpTypePointer Private %v3
  %ptrPrivateI = OpTypePointer Private %int

  %p0=OpConstantComposite %v3 %fn1 %fn1 %fn1
  %p1=OpConstantComposite %v3 %f1 %fn1 %fn1
  %p2=OpConstantComposite %v3 %f1 %f1 %fn1
  %p3=OpConstantComposite %v3 %fn1 %f1 %fn1
  %p4=OpConstantComposite %v3 %fn1 %fn1 %f1
  %p5=OpConstantComposite %v3 %f1 %fn1 %f1
  %p6=OpConstantComposite %v3 %f1 %f1 %f1
  %p7=OpConstantComposite %v3 %fn1 %f1 %f1
  %bias=OpConstantComposite %v3 %f025 %f025 %f025
  %positions=OpConstantComposite %arrPos %p0 %p1 %p2 %p3 %p4 %p5 %p6 %p7
  ; twelve edges, two endpoints per line
  %indices=OpConstantComposite %arrIdx
    %i0 %i1 %i1 %i2 %i2 %i3 %i3 %i0
    %i4 %i5 %i5 %i6 %i6 %i7 %i7 %i4
    %i0 %i4 %i1 %i5 %i2 %i6 %i3 %i7
  %vertexIndex = OpVariable %ptrInI Input
  %positionOut = OpVariable %ptrOutV4 Output
  %colorOut = OpVariable %ptrOutV3 Output
  %push = OpVariable %ptrPush PushConstant
  %positionsVar = OpVariable %ptrPrivatePos Private %positions
  %indicesVar = OpVariable %ptrPrivateIdx Private %indices

  %main = OpFunction %void None %fn
  %entry = OpLabel
  %vi = OpLoad %int %vertexIndex
  %ip = OpAccessChain %ptrPrivateI %indicesVar %vi
  %ix = OpLoad %int %ip
  %pp = OpAccessChain %ptrPrivateV3 %positionsVar %ix
  %p = OpLoad %v3 %pp
  %anglePtr = OpAccessChain %ptrPushF %push %i0
  %aspectPtr = OpAccessChain %ptrPushF %push %i1
  %angle = OpLoad %float %anglePtr
  %aspect = OpLoad %float %aspectPtr
  %s = OpExtInst %float %glsl Sin %angle
  %c = OpExtInst %float %glsl Cos %angle
  %x = OpCompositeExtract %float %p 0
  %y = OpCompositeExtract %float %p 1
  %z = OpCompositeExtract %float %p 2
  %cx = OpFMul %float %c %x
  %sz = OpFMul %float %s %z
  %rx = OpFAdd %float %cx %sz
  %sx = OpFMul %float %s %x
  %cz = OpFMul %float %c %z
  %rz0 = OpFSub %float %cz %sx
  %rz = OpFAdd %float %rz0 %f3
  %rxAspect = OpFDiv %float %rx %aspect
  %clipX = OpFDiv %float %rxAspect %rz
  %clipY = OpFDiv %float %y %rz
  %depth0 = OpFSub %float %rz %f1
  %depth = OpFDiv %float %depth0 %rz
  %clip = OpCompositeConstruct %v4 %clipX %clipY %depth %f1
  OpStore %positionOut %clip
  %half = OpVectorTimesScalar %v3 %p %f025
  %color = OpFAdd %v3 %half %bias
  OpStore %colorOut %color
  OpReturn
  OpFunctionEnd
}
```

The fragment shader has no hidden text/source representation:

<!-- grass-block: interface id=spike5-block-14 -->
```spirv
def cubeFragment : SpirvModule plan.shaderEnv := spirv_asm {
  OpCapability Shader
  OpMemoryModel Logical GLSL450
  OpEntryPoint Fragment %main "main" %colorIn %colorOut
  OpExecutionMode %main OriginUpperLeft
  OpDecorate %colorIn Location 0
  OpDecorate %colorOut Location 0
  %void=OpTypeVoid
  %fn=OpTypeFunction %void
  %float=OpTypeFloat 32
  %v3=OpTypeVector %float 3
  %v4=OpTypeVector %float 4
  %ptrInV3=OpTypePointer Input %v3
  %ptrOutV4=OpTypePointer Output %v4
  %f1=OpConstant %float 1.0
  %colorIn=OpVariable %ptrInV3 Input
  %colorOut=OpVariable %ptrOutV4 Output
  %main=OpFunction %void None %fn
  %entry=OpLabel
  %rgb=OpLoad %v3 %colorIn
  %r=OpCompositeExtract %float %rgb 0
  %g=OpCompositeExtract %float %rgb 1
  %b=OpCompositeExtract %float %rgb 2
  %rgba=OpCompositeConstruct %v4 %r %g %b %f1
  OpStore %colorOut %rgba
  OpReturn
  OpFunctionEnd
}
```

Review must reject any pseudo-instruction above that is not valid in the chosen
SPIR-V grammar. The arrays are module-scope `Private` variables with constant
initializers; there is no function-local aggregate-initialization shortcut.

## 7. Complete authored Win64 host machine source

The following is the whole authored machine source. `cubeHost` alone asserts no
cube behavior and no Win32/Vulkan refinement; those claims arise only when
`verify_assembly` consumes it with `processPlanRealizes` and the platform
contract. It uses two transparent
forms to keep ABI bookkeeping readable without hiding instructions:

- `win_call f(args) -> result` expands to literal Microsoft-x64 argument
  moves, stack arguments in the reserved outgoing area, indirect IAT call, and
  the declared clobbers; and
- `vk_call slot(args) -> VkResult` is the same literal expansion through the
  checked dispatch-table pointer.

Their expansions are part of `cubeHost`, visible in diagnostics and tunable per
call. They do not choose functions, insert branches, construct structures, or
discharge obligations. Every structure named below is a standard proved layout;
each brace lists every nonzero field and zero-initialization covers all others.

<!-- grass-block: interface id=spike5-block-15 -->
```text
def cubeHost : AsmSource plan := asm_source {
entry: @entry win64_gui_entry
  push rbx; push rbp; push rsi; push rdi; push r12; push r13; push r14; push r15
  sub rsp, FRAME_SIZE
  xor eax,eax; lea rdi,[rsp+locals]; mov ecx,LOCALS_QWORDS; rep stosq
  win_call GetProcessHeap() -> rax; test rax,rax; jz fail_init
  mov qword ptr [processHeap],rax
  win_call GetModuleHandleW(0) -> r12; test r12,r12; jz fail_init
  ; WNDCLASSEXW: cbSize/style/lpfnWndProc/hInstance/cursor/class name
  store32 wc.cbSize,SIZEOF_WNDCLASSEXW
  store32 wc.style,CS_HREDRAW|CS_VREDRAW|CS_OWNDC
  store64 wc.lpfnWndProc,&wndproc; store64 wc.hInstance,r12
  win_call LoadCursorW(0,IDC_ARROW) -> rax; store64 wc.hCursor,rax
  store64 wc.lpszClassName,&className
  win_call RegisterClassExW(&wc) -> eax; test ax,ax; jz fail_init
  mov byte ptr [ownership.classRegistered],1
  win_call CreateWindowExW(0,&className,&title,WS_OVERLAPPEDWINDOW,
      CW_USEDEFAULT,CW_USEDEFAULT,960,720,0,0,r12,&state) -> r13
  test r13,r13; jz fail_init
  mov byte ptr [state.hwndOwned],1
  win_call ShowWindow(r13,SW_SHOW) -> _
  win_call QueryPerformanceFrequency(&qpcFrequency) -> eax
  test eax,eax; jz fail_init
  cmp qword ptr [qpcFrequency],0; jle fail_init
  win_call QueryPerformanceCounter(&qpcEpoch) -> eax
  test eax,eax; jz fail_init
  mov rax,qword ptr [qpcEpoch]; mov qword ptr [qpcPrevious],rax
  jmp vk_instance

wndproc: @entry win64_callback(hwnd,msg,wparam,lparam)
  sub rsp,CALLBACK_FRAME_SIZE
  mov [rsp+callbackHwnd],rcx; mov [rsp+callbackMessage],edx
  mov [rsp+callbackWparam],r8; mov [rsp+callbackLparam],r9
  cmp edx,WM_NCCREATE; je wp_nccreate
  win_call GetWindowLongPtrW(rcx,GWLP_USERDATA) -> r10
  test r10,r10; jz wp_default
  mov edx,[rsp+callbackMessage]; mov r8,[rsp+callbackWparam]
  mov r9,[rsp+callbackLparam]
  cmp edx,WM_CLOSE; je wp_close
  cmp edx,WM_DESTROY; je wp_destroyed
  cmp edx,WM_NCDESTROY; je wp_ncdestroy
  cmp edx,WM_KEYDOWN; jne wp_size
  cmp r8d,VK_ESCAPE; je wp_close
wp_size:
  cmp edx,WM_SIZE; jne wp_default
  mov eax,r9d; and eax,0xffff; shr r9d,16
  store32 [r10+CubeWindowState.width],eax
  store32 [r10+CubeWindowState.height],r9d
  mov byte ptr [r10+CubeWindowState.resize],1
  xor eax,eax; add rsp,CALLBACK_FRAME_SIZE; ret
wp_nccreate:
  mov r10,[r9+CREATESTRUCTW.lpCreateParams]; test r10,r10; jz wp_reject_create
  mov [rsp+callbackState],r10
  win_call SetWindowLongPtrW(rcx,GWLP_USERDATA,r10) -> _
  mov rcx,[rsp+callbackHwnd]
  win_call GetWindowLongPtrW(rcx,GWLP_USERDATA) -> rax
  cmp rax,[rsp+callbackState]; jne wp_reject_create
  mov eax,1; add rsp,CALLBACK_FRAME_SIZE; ret
wp_reject_create:
  xor eax,eax; add rsp,CALLBACK_FRAME_SIZE; ret
wp_close:
  mov byte ptr [r10+CubeWindowState.exit],1
  xor eax,eax; add rsp,CALLBACK_FRAME_SIZE; ret
wp_destroyed:
  mov byte ptr [r10+CubeWindowState.exit],1
  mov byte ptr [r10+CubeWindowState.hwndOwned],0
  xor eax,eax; add rsp,CALLBACK_FRAME_SIZE; ret
wp_ncdestroy:
  mov byte ptr [r10+CubeWindowState.hwndOwned],0
  mov rcx,[rsp+callbackHwnd]
  win_call SetWindowLongPtrW(rcx,GWLP_USERDATA,0) -> _
  xor eax,eax; add rsp,CALLBACK_FRAME_SIZE; ret
wp_default:
  mov rcx,[rsp+callbackHwnd]; mov edx,[rsp+callbackMessage]
  mov r8,[rsp+callbackWparam]; mov r9,[rsp+callbackLparam]
  win_call DefWindowProcW(rcx,rdx,r8,r9) -> rax
  add rsp,CALLBACK_FRAME_SIZE; ret

vk_instance:
  ; VkApplicationInfo{apiVersion=VK_API_VERSION_1_3}; exact two extension names
  init appInfo {sType=APPLICATION_INFO,pApplicationName=&title,
      applicationVersion=1,pEngineName=&grass,engineVersion=1,
      apiVersion=VK_API_VERSION_1_3}
  init instanceCI {sType=INSTANCE_CREATE_INFO,pApplicationInfo=&appInfo,
      enabledExtensionCount=2,ppEnabledExtensionNames=&instanceExts}
  xor ecx,ecx; lea rdx,[vkCreateInstanceName]
  call qword ptr [rip+__imp_vkGetInstanceProcAddr]
  test rax,rax; jz fail_init; mov [vkCreateInstancePtr],rax
  mov rcx,&instanceCI; xor edx,edx; lea r8,[instance]
  call qword ptr [vkCreateInstancePtr]
  test eax,eax; jnz fail_init
  mov byte ptr [ownership.instanceOwned],1
  resolve_instance_functions_or_fail instance, instanceDispatch
  vk_call vkCreateWin32SurfaceKHR(instance,
      {sType=WIN32_SURFACE_CREATE_INFO_KHR,hinstance=r12,hwnd=r13},0,&surface)
  test eax,eax; jnz fail_init
  mov byte ptr [ownership.surfaceOwned],1

select_device:
  vk_call vkEnumeratePhysicalDevices(instance,&count,0); test eax,eax; jnz fail_init
  test count,count; jz fail_init
  checked_alloc count*8 -> devices; jz fail_init
  vk_call vkEnumeratePhysicalDevices(instance,&count,devices); test eax,eax; jnz fail_init
  ; finite scan: query properties/features/queue-family count and arrays; accept
  ; exactly api>=1.3, dynamicRendering, synchronization2, swapchain extension,
  ; one graphics family
  ; with vkGetPhysicalDeviceSurfaceSupportKHR true. Every allocation/count change
  ; is checked; VK_INCOMPLETE retries enumeration; exhausted scan -> fail_init.
  enumerate_and_select_literal_loop devices,count -> physical,qfamily
  test physical,physical; jz fail_init

create_device:
  init queueCI {sType=DEVICE_QUEUE_CREATE_INFO,queueFamilyIndex=qfamily,
      queueCount=1,pQueuePriorities=&one}
  init features13 {sType=PHYSICAL_DEVICE_VULKAN_1_3_FEATURES,
      dynamicRendering=1,synchronization2=1}
  init deviceCI {sType=DEVICE_CREATE_INFO,pNext=&features13,
      queueCreateInfoCount=1,pQueueCreateInfos=&queueCI,
      enabledExtensionCount=1,ppEnabledExtensionNames=&deviceExts}
  vk_call vkCreateDevice(physical,&deviceCI,0,&device); test eax,eax; jnz fail_init
  mov byte ptr [ownership.deviceOwned],1
  resolve_device_functions_or_fail device,deviceDispatch
  vk_call vkGetDeviceQueue(device,qfamily,0,&queue)
  jmp create_fixed

create_fixed:
  vk_call vkCreateCommandPool(device,
    {sType=COMMAND_POOL_CREATE_INFO,flags=RESET_COMMAND_BUFFER_BIT,
     queueFamilyIndex=qfamily},0,&commandPool); test eax,eax; jnz fail_init
  mov byte ptr [ownership.commandPoolOwned],1
  vk_call vkAllocateCommandBuffers(device,
    {sType=COMMAND_BUFFER_ALLOCATE_INFO,commandPool=commandPool,
     level=PRIMARY,commandBufferCount=1},&cmd); test eax,eax; jnz fail_init
  vk_call vkCreateSemaphore(device,{sType=SEMAPHORE_CREATE_INFO},0,&imageAvail)
  test eax,eax; jnz fail_init
  mov byte ptr [ownership.imageAvailOwned],1
  vk_call vkCreateSemaphore(device,{sType=SEMAPHORE_CREATE_INFO},0,&renderDone)
  test eax,eax; jnz fail_init
  mov byte ptr [ownership.renderDoneOwned],1
  vk_call vkCreateFence(device,{sType=FENCE_CREATE_INFO,flags=SIGNALED_BIT},0,&fence)
  test eax,eax; jnz fail_init
  mov byte ptr [ownership.fenceOwned],1
  ; exact embedded shader ranges are supplied directly
  vk_call vkCreateShaderModule(device,{sType=SHADER_MODULE_CREATE_INFO,
    codeSize=cubeVertexBytes.size,pCode=&cubeVertexBytes},0,&vertModule)
  test eax,eax; jnz fail_init
  mov byte ptr [ownership.vertModuleOwned],1
  vk_call vkCreateShaderModule(device,{sType=SHADER_MODULE_CREATE_INFO,
    codeSize=cubeFragmentBytes.size,pCode=&cubeFragmentBytes},0,&fragModule)
  test eax,eax; jnz fail_init
  mov byte ptr [ownership.fragModuleOwned],1
  vk_call vkCreatePipelineLayout(device,{sType=PIPELINE_LAYOUT_CREATE_INFO,
    pushConstantRangeCount=1,pPushConstantRanges=&{stageFlags=VERTEX_BIT,
    offset=0,size=8}},0,&pipelineLayout); test eax,eax; jnz fail_init
  mov byte ptr [ownership.pipelineLayoutOwned],1
  jmp recreate

recreate: @invariant fixed_objects_owned_and_no_swapchain_work
  mov eax,dword ptr [state.width]; test eax,eax; jz minimized_wait
  mov eax,dword ptr [state.height]; test eax,eax; jz minimized_wait
  vk_call vkDeviceWaitIdle(device); cmp eax,VK_SUCCESS; jne fail_runtime
  destroy_swapchain_views_pipeline_if_owned
  vk_call vkGetPhysicalDeviceSurfaceCapabilitiesKHR(physical,surface,&caps)
  test eax,eax; jnz surface_result
  test caps.supportedUsageFlags,VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT
  jz fail_runtime
  test caps.supportedCompositeAlpha,VK_COMPOSITE_ALPHA_OPAQUE_BIT_KHR
  jz fail_runtime
  vk_call vkGetPhysicalDeviceSurfaceFormatsKHR(physical,surface,&fmtCount,0)
  test eax,eax; jnz surface_result
  checked_alloc fmtCount*SIZEOF_FORMAT -> formats; jz fail_runtime
  vk_call vkGetPhysicalDeviceSurfaceFormatsKHR(physical,surface,&fmtCount,formats)
  test eax,eax; jnz surface_result
  select_required_format_or_fail formats,fmtCount -> surfaceFormat
  ; extent = fixed currentExtent or clamp(client extent,min,max); imageCount=min+1
  ; clamped to max when max!=0. Every arithmetic operation is checked.
  compute_extent_and_count caps,width,height -> extent,imageCount
  init swapCI {sType=SWAPCHAIN_CREATE_INFO_KHR,surface=surface,
    minImageCount=imageCount,imageFormat=B8G8R8A8_UNORM,
    imageColorSpace=SRGB_NONLINEAR_KHR,imageExtent=extent,imageArrayLayers=1,
    imageUsage=COLOR_ATTACHMENT_BIT,imageSharingMode=EXCLUSIVE,
    preTransform=caps.currentTransform,compositeAlpha=OPAQUE_BIT_KHR,
    presentMode=FIFO_KHR,clipped=1,oldSwapchain=oldSwapchain}
  vk_call vkCreateSwapchainKHR(device,&swapCI,0,&newSwapchain)
  test eax,eax; jnz surface_result
  destroy_old_swapchain_after_new_created
  vk_call vkGetSwapchainImagesKHR(device,swapchain,&imageCount,0)
  test eax,eax; jnz surface_result
  checked_alloc imageCount*8 -> images; jz fail_runtime
  checked_alloc imageCount*8 -> views; jz fail_runtime
  checked_alloc imageCount -> imageInitialized; jz fail_runtime
  vk_call vkGetSwapchainImagesKHR(device,swapchain,&imageCount,images)
  test eax,eax; jnz surface_result
create_view_loop: @measure imageCount-viewIndex
  cmp viewIndex,imageCount; je create_pipeline
  vk_call vkCreateImageView(device,{sType=IMAGE_VIEW_CREATE_INFO,
    image=images[viewIndex],viewType=TYPE_2D,format=B8G8R8A8_UNORM,
    components={IDENTITY,IDENTITY,IDENTITY,IDENTITY},subresourceRange=
    {aspectMask=COLOR_BIT,baseMipLevel=0,levelCount=1,
     baseArrayLayer=0,layerCount=1}},0,&views[viewIndex])
  test eax,eax; jnz fail_runtime
  inc viewIndex; jmp create_view_loop
create_pipeline:
  ; two stages main; no vertex input; line list; no culling; lineWidth=1;
  ; one viewport/scissor; no MSAA;
  ; no depth; one opaque color attachment; dynamic viewport/scissor/rendering.
  init shaderStages[0] {sType=PIPELINE_SHADER_STAGE_CREATE_INFO,
      stage=VERTEX_BIT,module=vertModule,pName=&mainName}
  init shaderStages[1] {sType=PIPELINE_SHADER_STAGE_CREATE_INFO,
      stage=FRAGMENT_BIT,module=fragModule,pName=&mainName}
  init emptyVertexInput {sType=PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO}
  init lineList {sType=PIPELINE_INPUT_ASSEMBLY_STATE_CREATE_INFO,
      topology=PRIMITIVE_TOPOLOGY_LINE_LIST,primitiveRestartEnable=0}
  init oneDynamicViewport {sType=PIPELINE_VIEWPORT_STATE_CREATE_INFO,
      viewportCount=1,scissorCount=1}
  init lineRaster {sType=PIPELINE_RASTERIZATION_STATE_CREATE_INFO,
      depthClampEnable=0,rasterizerDiscardEnable=0,polygonMode=POLYGON_MODE_FILL,
      cullMode=CULL_MODE_NONE,frontFace=FRONT_FACE_COUNTER_CLOCKWISE,
      depthBiasEnable=0,lineWidth=1.0f}
  init sample1 {sType=PIPELINE_MULTISAMPLE_STATE_CREATE_INFO,
      rasterizationSamples=SAMPLE_COUNT_1_BIT}
  init colorAttachment {blendEnable=0,
      colorWriteMask=R_BIT|G_BIT|B_BIT|A_BIT}
  init opaqueBlend {sType=PIPELINE_COLOR_BLEND_STATE_CREATE_INFO,
      attachmentCount=1,pAttachments=&colorAttachment}
  store32 dynamicStates[0],DYNAMIC_STATE_VIEWPORT
  store32 dynamicStates[1],DYNAMIC_STATE_SCISSOR
  init viewportScissor {sType=PIPELINE_DYNAMIC_STATE_CREATE_INFO,
      dynamicStateCount=2,pDynamicStates=&dynamicStates}
  init pipelineRendering {sType=PIPELINE_RENDERING_CREATE_INFO,
      colorAttachmentCount=1,pColorAttachmentFormats=&colorFormat}
  init graphicsCI {sType=GRAPHICS_PIPELINE_CREATE_INFO,pNext=&pipelineRendering,
      stageCount=2,pStages=&shaderStages,pVertexInputState=&emptyVertexInput,
      pInputAssemblyState=&lineList,pViewportState=&oneDynamicViewport,
      pRasterizationState=&lineRaster,pMultisampleState=&sample1,
      pColorBlendState=&opaqueBlend,pDynamicState=&viewportScissor,
      layout=pipelineLayout,renderPass=0,subpass=0}
  vk_call vkCreateGraphicsPipelines(device,0,1,&graphicsCI,0,&pipeline)
  test eax,eax; jnz fail_runtime
  mov byte ptr [state.resize],0; jmp event_loop

minimized_wait:
  cmp byte ptr [state.exit],0; jne clean_exit
  win_call WaitMessage() -> eax; test eax,eax; jz fail_runtime
  jmp pump_messages

event_loop: @frontier_or_measure(message_or_frame)
pump_messages:
  win_call PeekMessageW(&msg,0,0,0,PM_REMOVE) -> eax
  test eax,eax; jz messages_done
  cmp msg.message,WM_QUIT; je request_exit
  win_call TranslateMessage(&msg) -> _
  win_call DispatchMessageW(&msg) -> _
  jmp pump_messages
request_exit:
  mov byte ptr [state.exit],1
messages_done:
  cmp byte ptr [state.exit],0; jne clean_exit
  cmp byte ptr [state.resize],0; jne recreate
  vk_call vkWaitForFences(device,1,&fence,1,UINT64_MAX)
  cmp eax,VK_SUCCESS; jne device_result
  vk_call vkAcquireNextImageKHR(device,swapchain,UINT64_MAX,imageAvail,0,&imageIndex)
  cmp eax,VK_ERROR_OUT_OF_DATE_KHR; je recreate
  cmp eax,VK_SUBOPTIMAL_KHR; je acquired_suboptimal
  cmp eax,VK_SUCCESS; jne device_result
  mov byte ptr [state.recreateAfterPresent],0; jmp acquired
acquired_suboptimal:
  mov byte ptr [state.recreateAfterPresent],1
acquired:
  vk_call vkResetFences(device,1,&fence); cmp eax,VK_SUCCESS; jne device_result
  vk_call vkResetCommandBuffer(cmd,0); cmp eax,VK_SUCCESS; jne device_result
  vk_call vkBeginCommandBuffer(cmd,{sType=COMMAND_BUFFER_BEGIN_INFO,
      flags=ONE_TIME_SUBMIT_BIT}); cmp eax,VK_SUCCESS; jne device_result
  mov ecx,[imageIndex]
  init barrier {sType=IMAGE_MEMORY_BARRIER_2,
      dstStageMask=COLOR_ATTACHMENT_OUTPUT,dstAccessMask=COLOR_ATTACHMENT_WRITE,
      newLayout=COLOR_ATTACHMENT_OPTIMAL,image=images[rcx],
      subresourceRange={aspectMask=COLOR_BIT,baseMipLevel=0,levelCount=1,
      baseArrayLayer=0,layerCount=1}}
  cmp byte ptr [imageInitialized+rcx],0; je acquired_first_layout
  store32 barrier.oldLayout,PRESENT_SRC_KHR; jmp acquired_layout_ready
acquired_first_layout:
  store32 barrier.oldLayout,UNDEFINED; mov byte ptr [imageInitialized+rcx],1
acquired_layout_ready:
  init dependencyInfo {sType=DEPENDENCY_INFO,imageMemoryBarrierCount=1,
      pImageMemoryBarriers=&barrier}
  vk_call vkCmdPipelineBarrier2(cmd,&dependencyInfo)
  mov ecx,[imageIndex]
  init renderingAttachment {sType=RENDERING_ATTACHMENT_INFO,
      imageView=views[rcx],imageLayout=COLOR_ATTACHMENT_OPTIMAL,
      loadOp=CLEAR,storeOp=STORE,clearValue={0.02,0.02,0.04,1}}
  init rendering {sType=RENDERING_INFO,renderArea={0,extent},layerCount=1,
      colorAttachmentCount=1,pColorAttachments=&renderingAttachment}
  vk_call vkCmdBeginRendering(cmd,&rendering)
  vk_call vkCmdBindPipeline(cmd,GRAPHICS,pipeline)
  init viewport {width=float(extent.width),height=float(extent.height),maxDepth=1}
  init scissor {extent=extent}
  vk_call vkCmdSetViewport(cmd,0,1,&viewport)
  vk_call vkCmdSetScissor(cmd,0,1,&scissor)
  win_call QueryPerformanceCounter(&qpcNow) -> eax
  test eax,eax; jz fail_runtime
  mov rax,qword ptr [qpcNow]
  cmp rax,qword ptr [qpcPrevious]
  jl clock_violation @violation_edge(.monotonicClockRegressed)
  mov qword ptr [qpcPrevious],rax
  sub rax,qword ptr [qpcEpoch]
  jo clock_violation @violation_edge(.monotonicClockRangeExceeded)
  cvtsi2sd xmm1,rax
  cvtsi2sd xmm2,qword ptr [qpcFrequency]
  divsd xmm1,xmm2
  mulsd xmm1,qword ptr [angularVelocity]
  movapd xmm0,xmm1
  movapd xmm3,xmm0
  divsd xmm3,qword ptr [tau]
  roundsd xmm3,xmm3,1
  mulsd xmm3,qword ptr [tau]
  subsd xmm0,xmm3
  cvtsd2ss xmm0,xmm0
  cvtsi2ss xmm1,extent.width; cvtsi2ss xmm2,extent.height; divss xmm1,xmm2
  store32 push.angle,xmm0; store32 push.aspect,xmm1
  vk_call vkCmdPushConstants(cmd,pipelineLayout,VERTEX_BIT,0,8,&push)
  vk_call vkCmdDraw(cmd,24,1,0,0)
  vk_call vkCmdEndRendering(cmd)
  mov ecx,[imageIndex]
  init barrier {sType=IMAGE_MEMORY_BARRIER_2,
      srcStageMask=COLOR_ATTACHMENT_OUTPUT,srcAccessMask=COLOR_ATTACHMENT_WRITE,
      oldLayout=COLOR_ATTACHMENT_OPTIMAL,newLayout=PRESENT_SRC_KHR,
      image=images[rcx],subresourceRange={aspectMask=COLOR_BIT,baseMipLevel=0,
      levelCount=1,baseArrayLayer=0,layerCount=1}}
  vk_call vkCmdPipelineBarrier2(cmd,&dependencyInfo)
  vk_call vkEndCommandBuffer(cmd); cmp eax,VK_SUCCESS; jne device_result
  init waitSemaphoreInfo {sType=SEMAPHORE_SUBMIT_INFO,semaphore=imageAvail,
      stageMask=COLOR_ATTACHMENT_OUTPUT}
  init commandBufferInfo {sType=COMMAND_BUFFER_SUBMIT_INFO,commandBuffer=cmd}
  init signalSemaphoreInfo {sType=SEMAPHORE_SUBMIT_INFO,semaphore=renderDone,
      stageMask=ALL_GRAPHICS}
  init submit {sType=SUBMIT_INFO_2,waitSemaphoreInfoCount=1,
      pWaitSemaphoreInfos=&waitSemaphoreInfo,commandBufferInfoCount=1,
      pCommandBufferInfos=&commandBufferInfo,signalSemaphoreInfoCount=1,
      pSignalSemaphoreInfos=&signalSemaphoreInfo}
  vk_call vkQueueSubmit2(queue,1,&submit,fence); cmp eax,VK_SUCCESS; jne device_result
  init present {sType=PRESENT_INFO_KHR,waitSemaphoreCount=1,
      pWaitSemaphores=&renderDone,swapchainCount=1,pSwapchains=&swapchain,
      pImageIndices=&imageIndex}
  vk_call vkQueuePresentKHR(queue,&present)
  cmp eax,VK_ERROR_OUT_OF_DATE_KHR; je recreate
  cmp eax,VK_SUBOPTIMAL_KHR; je recreate
  cmp eax,VK_SUCCESS; jne device_result
  cmp byte ptr [state.recreateAfterPresent],0; jne recreate
  jmp event_loop

surface_result:
  cmp eax,VK_ERROR_SURFACE_LOST_KHR; je fail_surface
  cmp eax,VK_ERROR_OUT_OF_DATE_KHR; je recreate
  jmp fail_runtime
device_result:
  cmp eax,VK_ERROR_DEVICE_LOST; je fail_device
  cmp eax,VK_ERROR_SURFACE_LOST_KHR; je fail_surface
  jmp fail_runtime

clean_exit: mov ebx,0; jmp cleanup
fail_init: mov ebx,1; jmp cleanup
fail_runtime: mov ebx,2; jmp cleanup
fail_surface: mov ebx,3; mov byte ptr [ownership.surfaceLost],1; jmp cleanup
fail_device: mov ebx,4; mov byte ptr [ownership.deviceLost],1; jmp cleanup
clock_violation:
  ud2 @containment_tail(.monotonicClockRegressed)

cleanup: @placement [status := ebx]
         @invariant reverse_dependency_ledger
  reverse_cleanup
  add rsp,FRAME_SIZE; pop r15; pop r14; pop r13; pop r12
  pop rdi; pop rsi; pop rbp; pop rbx
  mov ecx,ebx; call qword ptr [rip+__imp_ExitProcess]; ud2
}
```

Decision 42 forbids contracts from standing in for any algorithmic, API,
flow-control, error, or cleanup body. The abbreviated spellings above are
accepted only as transparent macros with the following displayed expansions.
Every instantiation is present in the pretty-printed raw listing and may be
replaced by arbitrary literal assembly.

As required by [INSTRUCTIONS.md](INSTRUCTIONS.md), `asm_source` emits stable,
alpha-normalized per-block declarations and a source manifest. Process routing
does not add a hidden scheduler macro or new instruction: each process boundary
above is a proved interpretation of the literal blocks and API calls displayed
here. Review diagnostics include the complete macro-expanded source and every
separately cached block certificate.

### 7.1 Mechanical call and structure expansions

The macros are finite syntax transformers, not proof-producing or
provider-selecting operations. Their complete expansion function is:

<!-- grass-block: proof-sketch id=spike5-block-16 -->
```lean
def win64ArgLocation : Nat -> CallLocation
  | 0 => .register .rcx
  | 1 => .register .rdx
  | 2 => .register .r8
  | 3 => .register .r9
  | n + 4 => .stack (32 + 8 * n)

def expandArguments (arguments : Vec Operand) : Vec RawInstruction :=
  -- Stack destinations are emitted from highest index down. Register
  -- destinations use the proved deterministic parallel-move algorithm with
  -- r11 and the reserved call-spill slot to break every overlap cycle.
  ParallelMove.expand
    (arguments.mapIdx fun index argument =>
      (argument, win64ArgLocation index))

def expandCall (target : CallTarget) (arguments : Vec Operand)
    (result : Option Register) : Vec RawInstruction :=
  expandArguments arguments ++
  #[match target with
    | .iat symbol => callMem (.ripRelative (iatSymbol symbol))
    | .dispatch base slot => callMem (.baseDisplacement base slot)] ++
  match result with
  | none => #[]
  | some .rax => #[]
  | some destination => #[mov destination .rax]
```

`ParallelMove.expand` is an instruction-only standard-library function with a
writer/reader round trip and a forall theorem that final destinations equal the
simultaneous assignment while all non-destinations except `r11` and the named
spill are framed. It is not a tactic and contributes its returned instructions
to `cubeHost` identity. The frame reserves the maximum stack-argument extent,
four register staging locations, and the one call-spill location required by
every displayed call.

Each invocation's argument vector is the complete comma-delimited vector shown
in section 7; there is no implicit argument. `_` means `result := none`.
`init S {fields}` expands to `xor eax,eax; lea rdi,S; mov
ecx,sizeof(S)/8; rep stosq`, followed in source order by one width-correct `mov
[S+provedOffset],value` for every displayed field. `store32` and `store64` are
exactly their single width-matched `mov`. Unsigned `clamp value low high`
expands to `cmp value,low; cmovb value,low; cmp value,high; cmova value,high`;
the source branches around the final pair when Vulkan declares `high = 0`.
`exit_with status` expands exactly to `mov ecx,status; call qword ptr
[rip+__imp_ExitProcess]; ud2`, where the unreachable `ud2` makes an erroneous
provider return a modeled fault rather than fall-through. These macros contain
no hidden control choice, provider choice, or obligation discharge.

The entry calls `GetProcessHeap`. Allocation and release expand exactly as
follows (`count`, `stride`, pointer, and tag are macro parameters):

<!-- grass-block: proof-sketch id=spike5-block-17 -->
```text
mov pointer,0; mov byte ptr [tag],0
mov rax,count; mov rcx,stride; mul rcx
test rdx,rdx; jnz allocation_failed
test count,count; jz allocation_failed
test rax,rax; jz allocation_failed
mov r8,rax; mov rcx,[processHeap]; xor edx,edx
call qword ptr [rip+__imp_HeapAlloc]
test rax,rax; jz allocation_failed
mov pointer,rax; mov byte ptr [tag],1
mov eax,1; jmp allocation_done
allocation_failed: xor eax,eax
allocation_done: test eax,eax
; @ghost fresh_allocation(pointer, count*stride)

free_head: cmp byte ptr [tag],0; je free_done
mov rcx,[processHeap]; xor edx,edx; mov r8,pointer
call qword ptr [rip+__imp_HeapFree]
test eax,eax; jz provider_violation @violation_edge(.ownedHeapFreeRejected)
mov pointer,0; mov byte ptr [tag],0
free_done:
```

The allocation fragment owns both local continuations and returns success in
the flags tested by the following authored branch. It cannot jump to an ambient
label. The derived imports therefore include `GetProcessHeap`, `HeapAlloc`, and
`HeapFree`.

### 7.2 Dispatch-table expansion

The following literal loops replace both resolver abbreviations. The static
name arrays contain exactly the slots used in section 7.

<!-- grass-block: proof-sketch id=spike5-block-18 -->
```text
resolve_i_init: xor r14d,r14d
resolve_i_head: @measure instanceSlotCount-r14
  cmp r14d,instanceSlotCount; je resolve_i_seal
  mov rcx,[instance]; mov rdx,[instanceNames+r14*8]
  call qword ptr [rip+__imp_vkGetInstanceProcAddr]
  test rax,rax; jz fail_init
  mov [instanceDispatch+r14*8],rax; inc r14d; jmp resolve_i_head
resolve_i_seal: @ghost seal_read_only(instanceDispatch); jmp select_device

resolve_d_init: xor r14d,r14d
resolve_d_head: @measure deviceSlotCount-r14
  cmp r14d,deviceSlotCount; je resolve_d_seal
  mov rcx,[device]; mov rdx,[deviceNames+r14*8]
  call qword ptr [rip+__imp_vkGetDeviceProcAddr]
  test rax,rax; jz fail_init
  mov [deviceDispatch+r14*8],rax; inc r14d; jmp resolve_d_head
resolve_d_seal: @ghost seal_read_only(deviceDispatch); jmp create_fixed
```

### 7.3 Enumeration and selection expansion

Every count/fill pair follows this literal scheme: query count, checked-allocate
`count*stride`, initialize required `sType` fields, fill, and on `VK_INCOMPLETE`
free and restart at the count query. Other non-success returns take the printed
failure edge. Device selection expands to:

<!-- grass-block: proof-sketch id=spike5-block-19 -->
```text
dev_init: xor r14d,r14d
dev_head: @measure deviceCount-r14
  cmp r14d,[deviceCount]; je fail_init
  mov r15,[devices+r14*8]
  init properties2 {sType=PHYSICAL_DEVICE_PROPERTIES_2}
  vk_call vkGetPhysicalDeviceProperties2(r15,&properties2)
  cmp [properties.apiVersion],VK_API_VERSION_1_3; jb dev_next
  init features13 {sType=PHYSICAL_DEVICE_VULKAN_1_3_FEATURES}
  init features2 {sType=PHYSICAL_DEVICE_FEATURES_2,pNext=&features13}
  vk_call vkGetPhysicalDeviceFeatures2(r15,&features2)
  cmp [features13.dynamicRendering],0; je dev_next
  cmp [features13.synchronization2],0; je dev_next
ext_count:
  vk_call vkEnumerateDeviceExtensionProperties(r15,0,&extCount,0)
  cmp eax,VK_SUCCESS; jne dev_next
  checked_alloc extCount*SIZEOF_EXTENSION_PROPERTIES -> extProps
  vk_call vkEnumerateDeviceExtensionProperties(r15,0,&extCount,extProps)
  cmp eax,VK_INCOMPLETE; je ext_retry
  cmp eax,VK_SUCCESS; jne dev_next_free_ext
  xor ebx,ebx
ext_head: @measure extCount-rbx
  cmp ebx,[extCount]; je dev_next_free_ext
  lea rsi,[extProps+rbx*EXTSIZE+extensionName]; lea rdi,[swapchainExtName]
  xor ecx,ecx
ext_char: @measure VK_MAX_EXTENSION_NAME_SIZE-rcx
  cmp ecx,VK_MAX_EXTENSION_NAME_SIZE; je dev_next_free_ext
  mov al,[rsi+rcx]; cmp al,[rdi+rcx]; jne ext_next
  test al,al; jz ext_found
  inc ecx; jmp ext_char
ext_next: inc ebx; jmp ext_head
ext_found:
  vk_call vkGetPhysicalDeviceQueueFamilyProperties2(r15,&queueCount,0)
  checked_alloc queueCount*SIZEOF_QUEUE_PROPERTIES_2 -> queueProps
  xor ebx,ebx
queue_init: @measure queueCount-rbx
  cmp ebx,[queueCount]; je queue_fill
  zero [queueProps+rbx*QSIZE],QSIZE
  mov [queueProps+rbx*QSIZE+sType],PHYSICAL_DEVICE_QUEUE_FAMILY_PROPERTIES_2
  inc ebx; jmp queue_init
queue_fill:
  vk_call vkGetPhysicalDeviceQueueFamilyProperties2(r15,&queueCount,queueProps)
  xor ebx,ebx
queue_head: @measure queueCount-rbx
  cmp ebx,[queueCount]; je dev_next_free_all
  test [queueProps+rbx*QSIZE+queueFlags],VK_QUEUE_GRAPHICS_BIT; jz queue_next
  vk_call vkGetPhysicalDeviceSurfaceSupportKHR(r15,ebx,[surface],&supported)
  cmp eax,VK_SUCCESS; jne dev_next_free_all
  cmp [supported],0; jne dev_selected
queue_next: inc ebx; jmp queue_head
dev_selected:
  mov [physical],r15; mov [qfamily],ebx
  free queueProps; free extProps; free devices; jmp create_device
dev_next_free_all: free queueProps
dev_next_free_ext: free extProps
dev_next: inc r14d; jmp dev_head
ext_retry: free extProps; jmp ext_count
```

`zero` above is only the displayed `xor eax,eax; lea rdi,address; mov
ecx,size/8; rep stosq`. No callback or hidden iterator is involved.

### 7.4 Format, extent, image state, and recreation expansion

<!-- grass-block: proof-sketch id=spike5-block-20 -->
```text
fmt_init: xor ebx,ebx
fmt_head: @measure fmtCount-rbx
  cmp ebx,[fmtCount]; je fail_runtime_free_formats
  cmp [formats+rbx*FSIZE+format],VK_FORMAT_B8G8R8A8_UNORM; jne fmt_next
  cmp [formats+rbx*FSIZE+colorSpace],VK_COLOR_SPACE_SRGB_NONLINEAR_KHR; je fmt_found
fmt_next: inc ebx; jmp fmt_head
fmt_found: free formats
  cmp [caps.currentExtent.width],UINT32_MAX; jne extent_fixed
  mov eax,[state.width]; cmp eax,[caps.min.width]; cmovb eax,[caps.min.width]
  cmp eax,[caps.max.width]; cmova eax,[caps.max.width]; mov [extent.width],eax
  mov eax,[state.height]; cmp eax,[caps.min.height]; cmovb eax,[caps.min.height]
  cmp eax,[caps.max.height]; cmova eax,[caps.max.height]; mov [extent.height],eax
  jmp extent_done
extent_fixed: mov rax,[caps.currentExtent]; mov [extent],rax
extent_done:
  cmp [extent.width],0; je minimized_wait
  cmp [extent.height],0; je minimized_wait
  mov eax,[caps.minImageCount]; cmp eax,UINT32_MAX; je fail_runtime
  inc eax; mov ecx,[caps.maxImageCount]; test ecx,ecx; jz count_done
  cmp eax,ecx; cmova eax,ecx
count_done: mov [imageCount],eax
```

Each swapchain generation owns `images`, `views`, and one byte of layout state
per image. Every byte starts zero. The first use chooses `UNDEFINED`; later uses
choose `PRESENT_SRC_KHR`:

<!-- grass-block: proof-sketch id=spike5-block-21 -->
```text
mov ecx,[imageIndex]
cmp byte ptr [imageInitialized+rcx],0; je layout_undefined
mov [barrier.oldLayout],VK_IMAGE_LAYOUT_PRESENT_SRC_KHR; jmp layout_ready
layout_undefined:
mov [barrier.oldLayout],VK_IMAGE_LAYOUT_UNDEFINED
mov byte ptr [imageInitialized+rcx],1
layout_ready:
mov [barrier.newLayout],VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL
```

Old generation destruction, after `vkDeviceWaitIdle`, is literal:

<!-- grass-block: proof-sketch id=spike5-block-22 -->
```text
destroy_old_init: mov ecx,[initializedViewCount]
destroy_old_head: @measure ecx
  test ecx,ecx; jz destroy_old_pipeline
  dec ecx; vk_call vkDestroyImageView(device,views[rcx],0)
  mov qword ptr [views+rcx*8],0; jmp destroy_old_head
destroy_old_pipeline:
  cmp pipelineOwned,0; je destroy_old_swap
  vk_call vkDestroyPipeline(device,pipeline,0); mov pipelineOwned,0
destroy_old_swap:
  cmp swapchainOwned,0; je destroy_old_arrays
  vk_call vkDestroySwapchainKHR(device,swapchain,0); mov swapchainOwned,0
destroy_old_arrays: free imageInitialized; free views; free images
```

### 7.5 Reverse cleanup expansion

Device loss skips the idle wait but does not silently adopt resources. The
selected Vulkan failure profile must authorize each destroy call after loss.

<!-- grass-block: proof-sketch id=spike5-block-23 -->
```text
cleanup:
  cmp deviceOwned,0; je cleanup_views
  cmp deviceLost,0; jne cleanup_views
  vk_call vkDeviceWaitIdle(device)
cleanup_views: mov ecx,initializedViewCount
cleanup_view_head: test ecx,ecx; jz cleanup_pipeline
  dec ecx; vk_call vkDestroyImageView(device,views[rcx],0); jmp cleanup_view_head
cleanup_pipeline: cmp pipelineOwned,0; je cleanup_swap
  vk_call vkDestroyPipeline(device,pipeline,0)
cleanup_swap: cmp swapchainOwned,0; je cleanup_layout
  vk_call vkDestroySwapchainKHR(device,swapchain,0)
cleanup_layout: cmp layoutOwned,0; je cleanup_frag
  vk_call vkDestroyPipelineLayout(device,pipelineLayout,0)
cleanup_frag: cmp fragOwned,0; je cleanup_vert
  vk_call vkDestroyShaderModule(device,fragModule,0)
cleanup_vert: cmp vertOwned,0; je cleanup_fence
  vk_call vkDestroyShaderModule(device,vertModule,0)
cleanup_fence: cmp fenceOwned,0; je cleanup_sem1
  vk_call vkDestroyFence(device,fence,0)
cleanup_sem1: cmp renderDoneOwned,0; je cleanup_sem2
  vk_call vkDestroySemaphore(device,renderDone,0)
cleanup_sem2: cmp imageAvailOwned,0; je cleanup_pool
  vk_call vkDestroySemaphore(device,imageAvail,0)
cleanup_pool: cmp poolOwned,0; je cleanup_device
  vk_call vkDestroyCommandPool(device,commandPool,0)
cleanup_device: cmp deviceOwned,0; je cleanup_surface
  vk_call vkDestroyDevice(device,0)
cleanup_surface: cmp surfaceOwned,0; je cleanup_instance
  vk_call vkDestroySurfaceKHR(instance,surface,0)
cleanup_instance: cmp instanceOwned,0; je cleanup_heap
  vk_call vkDestroyInstance(instance,0)
cleanup_heap: free imageInitialized; free views; free images
  free queueProps; free extProps; free devices
  cmp hwndOwned,0; je cleanup_class; win_call DestroyWindow(hwnd)
cleanup_class: cmp classRegistered,0; je cleanup_return
  win_call UnregisterClassW(&className,hInstance)
cleanup_return:
  add rsp,FRAME_SIZE; pop r15; pop r14; pop r13; pop r12
  pop rdi; pop rsi; pop rbp; pop rbx; exit_with ebx
```

Before implementation review, the pretty-printer must inline every macro
instantiation into one line-auditable raw listing. A contract alone cannot
satisfy this section. No C, GLSL, windowing helper, Vulkan helper, allocator
runtime, or hidden exception path exists in the artifact.

The current comment-free spike expresses the authored source through
`Layout.lean`, `Macros.lean`, and `Assembly.lean`. `Layout.lean` selects concrete
ABI layouts and dispatch names; `Macros.lean` contains transparent host
constructors; `Assembly.lean` owns static objects, both SPIR-V modules, and the
literal host source. `Program.lean` composes the host and shaders as `source`
and passes that term to `verify_assembly`.

This is not yet enough to claim source closure. The final closing form must take
the selected layout, macro registry, static-object table, rotation
representation theorem, callback-state theorem, and cross-ISA host/shader
connection as explicit dependent inputs or derive them uniquely from `source`.
It must produce one canonical raw host listing and a manifest containing exact
shader words, imports, relocations, symbols, layouts, and source maps. The
present corpus has **not generated** that listing or manifest, and their check
cost is **not measured**. Ambient namespace discovery is forbidden. Changing
any connected input must change machine-source identity and invalidate the first
adjacent certificate.

This remains an expected-source design fixture, not build evidence: the future
`Grass.*` modules, elaborator, verifier, and printer do not yet exist, so the
displayed theorem terms have not run and no generated byte-level listing is
claimed. What is reviewable now is the complete local body/manifest shape and
every intended adjacency. Implementation acceptance additionally requires the
printer's fully instantiated raw listing to be checked against this manifest;
until then the spike is defensible design input, not a verified executable.

### 7.6 Static data, dispatch names, and imports

The authored static objects are: UTF-16 `className = "GrassCube\0"` and
`title = "Grass Vulkan Cube\0"`; ASCII `grass`, `VK_KHR_surface`,
`VK_KHR_win32_surface`, and `VK_KHR_swapchain`; `one = 1.0f`,
`angularVelocity = 0.6` radians/second, and `tau = 6.283185307179586` as
binary64 values; the two shader-word arrays; and the
complete function-name arrays below. There is no generated geometry blob.
`vkCreateInstanceName`, `swapchainExtName`, `mainName`, and the addressable
`colorFormat` enum word are separate named static objects. The mutable
`vkCreateInstancePtr` is instead an entry-frame pointer and never appears in
read-only data.

`cubeFrameLayout` packs the window state, clock fields, all handles and counts,
allocation pointers, dispatch tables, ownership ledger, every Vulkan create or
submit structure, both shader-stage records, pipeline fixed-function records,
barriers, dynamic-rendering records, and outgoing-call/spill storage.
`cubeCallbackFrameLayout` separately packs the four saved callback arguments,
recovered state pointer, outgoing-call area, and move spill. The reviewed
manifest names both layouts, every static symbol, every authored block, and
every literal expansion fragment. `cubeSymbolResolutionExact` and
`cubeFrameLifetimesNonoverlapping` are required before the no-unresolved-form
claim can be used.

<!-- grass-block: interface id=spike5-block-24 -->
```text
instanceNames = [
 vkDestroyInstance, vkCreateWin32SurfaceKHR, vkDestroySurfaceKHR,
 vkEnumeratePhysicalDevices, vkGetPhysicalDeviceProperties2,
 vkGetPhysicalDeviceFeatures2, vkEnumerateDeviceExtensionProperties,
 vkGetPhysicalDeviceQueueFamilyProperties2,
 vkGetPhysicalDeviceSurfaceSupportKHR,
 vkGetPhysicalDeviceSurfaceCapabilitiesKHR,
 vkGetPhysicalDeviceSurfaceFormatsKHR, vkCreateDevice ]

deviceNames = [
 vkDestroyDevice, vkGetDeviceQueue, vkCreateCommandPool,
 vkDestroyCommandPool, vkAllocateCommandBuffers, vkCreateSemaphore,
 vkDestroySemaphore, vkCreateFence, vkDestroyFence, vkCreateShaderModule,
 vkDestroyShaderModule, vkCreatePipelineLayout, vkDestroyPipelineLayout,
 vkCreateSwapchainKHR, vkDestroySwapchainKHR, vkGetSwapchainImagesKHR,
 vkCreateImageView, vkDestroyImageView, vkCreateGraphicsPipelines,
 vkDestroyPipeline, vkDeviceWaitIdle, vkWaitForFences,
 vkAcquireNextImageKHR, vkResetFences, vkResetCommandBuffer,
 vkBeginCommandBuffer, vkCmdPipelineBarrier2, vkCmdBeginRendering,
 vkCmdBindPipeline, vkCmdSetViewport, vkCmdSetScissor,
 vkCmdPushConstants, vkCmdDraw, vkCmdEndRendering, vkEndCommandBuffer,
 vkQueueSubmit2, vkQueuePresentKHR ]
```

The exact derived PE imports are `GetModuleHandleW`, `LoadCursorW`,
`RegisterClassExW`, `CreateWindowExW`, `ShowWindow`, `DestroyWindow`,
`DefWindowProcW`, `GetWindowLongPtrW`, `SetWindowLongPtrW`, `WaitMessage`,
`PeekMessageW`, `TranslateMessage`,
`DispatchMessageW`, `UnregisterClassW`, `QueryPerformanceFrequency`,
`QueryPerformanceCounter`, `GetProcessHeap`, `HeapAlloc`,
`HeapFree`, and `ExitProcess`, plus `vkGetInstanceProcAddr` and
`vkGetDeviceProcAddr`. The verified linker rejects any mismatch between this
set, the IAT, and reachable call sites.

The pipeline component names in `graphicsCI` expand to these complete nonzero
fields; all structures are first zeroed by the displayed `init` expansion:

<!-- grass-block: interface id=spike5-block-25 -->
```text
shaderStages[0] {sType=PIPELINE_SHADER_STAGE_CREATE_INFO,
  stage=VERTEX_BIT,module=vertModule,pName=&mainName}
shaderStages[1] {sType=PIPELINE_SHADER_STAGE_CREATE_INFO,
  stage=FRAGMENT_BIT,module=fragModule,pName=&mainName}
emptyVertexInput {sType=PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO}
lineList {sType=PIPELINE_INPUT_ASSEMBLY_STATE_CREATE_INFO,
  topology=PRIMITIVE_TOPOLOGY_LINE_LIST,primitiveRestartEnable=0}
oneDynamicViewport {sType=PIPELINE_VIEWPORT_STATE_CREATE_INFO,
  viewportCount=1,scissorCount=1}
lineRaster {sType=PIPELINE_RASTERIZATION_STATE_CREATE_INFO,
  depthClampEnable=0,rasterizerDiscardEnable=0,polygonMode=POLYGON_MODE_FILL,
  cullMode=CULL_MODE_NONE,frontFace=FRONT_FACE_COUNTER_CLOCKWISE,
  depthBiasEnable=0,lineWidth=1.0f}
sample1 {sType=PIPELINE_MULTISAMPLE_STATE_CREATE_INFO,
  rasterizationSamples=SAMPLE_COUNT_1_BIT}
colorAttachment {blendEnable=0,
  colorWriteMask=R_BIT|G_BIT|B_BIT|A_BIT}
opaqueBlend {sType=PIPELINE_COLOR_BLEND_STATE_CREATE_INFO,
  attachmentCount=1,pAttachments=&colorAttachment}
dynamicStates [DYNAMIC_STATE_VIEWPORT,DYNAMIC_STATE_SCISSOR]
viewportScissor {sType=PIPELINE_DYNAMIC_STATE_CREATE_INFO,
  dynamicStateCount=2,pDynamicStates=&dynamicStates}
```

The command barrier, rendering attachment, submission, and presentation
structures likewise list every nonzero field at their call site. Their nested
one-element records are materialized in the host frame, not temporary syntax
whose lifetime could end before the call.

## 8. Cross-ISA connection and exact emission

The shader modules are serialized independently, then embedded as aligned,
read-only PE data:

<!-- grass-block: proof-sketch id=spike5-block-26 -->
```lean
def vertexWords : Vec UInt32 := Spirv.writeWords cubeVertex
def fragmentWords : Vec UInt32 := Spirv.writeWords cubeFragment

theorem vertex_round_trip : Spirv.parseWords vertexWords = .ok cubeVertex
theorem fragment_round_trip : Spirv.parseWords fragmentWords = .ok cubeFragment

theorem process_plan_exact : cubeVerified.process.plan = processPlan := rfl

theorem machine_source_exact : cubeVerified.machineSource = source := rfl

structure CrossIsaArtifactConnection (artifact : Artifact cubeVerified.realization) where
  process : ProcessPlanRealizes spec cubeVerified.process.plan
  driver : ProcessDriver spec cubeVerified.process.plan
    cubeVerified.process.correct cubeVerified.realization cubeVerified.ghostProgram
  assembly : AssemblyImplements
    cubeVerified.platformContract cubeVerified.machineSource
  exactArtifact : artifact = cubeVerified.linkedArtifact
  host : PETextRepresents cubeVerified.rawProgram.host artifact
  vertexRange : ExactReadOnlyRange artifact vertexWords
  fragmentRange : ExactReadOnlyRange artifact fragmentWords
  vertexCall : EveryShaderCreateUse host.trace `vertex = vertexRange
  fragmentCall : EveryShaderCreateUse host.trace `fragment = fragmentRange
  vertexModule : PipelineStageUsesCreatedModule
    host.trace `vertex `main vertexCall
  fragmentModule : PipelineStageUsesCreatedModule
    host.trace `fragment `main fragmentCall
  provider : VulkanConsumesSpirvSemantics
    plan vertexWords fragmentWords vertexCorrect fragmentCorrect
```

`VulkanConsumesSpirvSemantics` is not a theorem that arbitrary drivers are
correct. It is the cited platform model parameter challenged by validators and
physical probes. Inside the model it connects pipeline creation, interface
matching, push-constant bytes, draw invocations, rasterization, synchronization,
and presentation to both SPIR-V execution relations. `vertexModule` and
`fragmentModule` make the created handle identity and `"main"` pipeline-stage
entry point exact; an unrelated proved module cannot satisfy the junction. The final behavioral
theorem composes x86 host steps and GPU shader invocations under one namespaced
choice oracle and one obligation ledger.

The artifact mutation suite independently changes each shader RVA, `codeSize`,
`pCode`, returned shader-module handle, pipeline-stage module, `pName`, and one
embedded word. Each mutation must fail at the first corresponding field of
`CrossIsaArtifactConnection`; success of PE parsing or byte-range containment
alone is deliberately insufficient.

The PE contains `.text`, read-only constants and shader words, `.data`, `.idata`,
`.reloc`, `.pdata`, and `.xdata`. It imports the listed Win32 APIs plus the two
Vulkan resolver exports; the derived import set rejects unused or missing
entries. ASLR remains enabled, every host/shader address is abstract until
layout, final permissions are standard, and shader `pCode` alignment and
`codeSize mod 4 = 0` are proved.

<!-- grass-block: proof-sketch id=spike5-block-27 -->
```lean
theorem artifact_connection :
  CrossIsaArtifactConnection cubeVerified.linkedArtifact

theorem pe_round_trip :
  PE.parse (PE.write cubeVerified.linkedArtifact) =
    .ok cubeVerified.linkedArtifact

theorem bytes_exact :
  emitProgram cubeVerified = PE.write cubeVerified.linkedArtifact

-- `cubeVerified.sound` quantifies over every admissible process population and
-- routing history, load base, import environment, Win32/Vulkan response
-- strategy, scheduler, and GPU execution.
```

## 9. Validation and citation anchors

Every used x86 instruction cites both the Intel and AMD manuals through the
common profile. Every Win32 function, Vulkan command/structure/result, SPIR-V
instruction, execution-environment rule, PE field, and ABI rule gets a
declaration-level citation record and review instructions.

Required authoritative roots include:

- Khronos, Vulkan specification, including initialization, WSI, synchronization,
  dynamic rendering, shaders, and valid-usage clauses:
  https://registry.khronos.org/vulkan/specs/latest-ratified/html/vkspec.html
- Khronos, SPIR-V unified specification and binary form:
  https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html
- Khronos, Vulkan SPIR-V environment appendix:
  https://registry.khronos.org/vulkan/specs/latest-ratified/html/vkspec.html#spirvenv
- Microsoft, window creation and message-loop references:
  https://learn.microsoft.com/en-us/windows/win32/learnwin32/creating-a-window
  and https://learn.microsoft.com/en-us/windows/win32/learnwin32/window-messages
- Microsoft, PE format and x64 calling convention, already registered in
  [REFERENCES.md](REFERENCES.md).

Validation campaigns include SPIR-V grammar/validator differential tests,
writer/parser mutation fuzzing, shader-interface reflection, Vulkan validation
layers, API result/count/resize/minimize/device-loss probes, synchronization
validation, loader/relocation mutation, software Vulkan implementations where
useful, and physical runs across named Intel/AMD hosts and multiple GPU vendors.
Screenshots are weak smoke tests; probes compare modeled frame invariants,
reported validation events, resource lifetimes, and complete API traces.
Process-model validation additionally mutates demand/result occurrence identities,
reorders only channel-permitted events, injects close during every precommit and
postcommit phase, forces acquire/present recreation and device/surface loss, and
checks the process-to-CFG interval map covers every reachable API call and
callback. These tests challenge the model; they do not replace the universal
driver and machine proofs.

Source-closure mutations delete or rename each reviewed static symbol and frame
object in turn, remove each `shaderStages` field initialization, exchange the
vertex and fragment module handles, remove either user-data import, dispatch
`WM_SIZE` synchronously from `CreateWindowExW`, clear `GWLP_USERDATA` early, and
move entry-frame release before `WM_NCDESTROY`. The first adjacent symbol,
layout, pipeline, callback-lifetime, or host-refinement certificate must fail.
The raw-manifest test also deletes each local macro fragment body while retaining
its registry name; a name without reviewed instructions must not elaborate.

## 10. Proof economy and SDLC invalidation

| Reviewed change | Must recheck | Must remain reusable |
| --- | --- | --- |
| semantic scene/color law | `scene`, root process proofs, affected shader refinement and words, plan observation refinement, PE | window/input child and unrelated host init blocks |
| nonsemantic physical palette tuning inside the accepted image envelope | fragment module, pipeline connection, embedded words, PE | precious specification function, selected resources, host source, vertex proof |
| vertex geometry/rotation realization | vertex module and scene refinement, embedded words, PE | root transition proof, host source except interface hash, fragment proof |
| root update rule only | `cubeApplicationCorrect`, top observation refinement, affected driver boundary | unchanged child protocols, machine blocks, shaders whose boundary still matches |
| process topology/channel routing only | `processPlan`, population/weave/driver proof, affected process-to-block mapping | precious specification function, selected resources, and unchanged local block/shader certificates |
| one to several frames in flight | nonprecious process plan, channel/loan/progress proof, graphics blocks and resource ledger | precious specification function, selected resources, window child, shader semantic proofs |
| host register/instruction tuning | affected local x86 blocks, process-to-block interval proof, unwind if frame changes, PE | precious specification function, selected resources, and both shader semantic proofs |
| resize implementation policy | portable observation only if semantics change; otherwise window/recreation child and mapped blocks | root process proof when events/commits are unchanged, shader proofs and unrelated init blocks |
| Vulkan profile/version | provider laws, affected valid usage, device selection, cross-ISA bridge | portable scene specification |
| input termination semantics | precious specification function and message/cancellation/cleanup cone | selected resource value unless its interface changes; shader modules and graphics math |
| PE layout only | artifact connection, loader, exact bytes | host/shader semantic certificates |

The dependency report must show these causal paths. A process weave edit must
not change the root process type; a shader edit must not re-prove the Win32
message loop; an x86 scheduling edit must not re-prove cube geometry; a PE
alignment edit must not re-prove either ISA semantics. Interface hashes may
cause the narrow pipeline-compatibility certificate to regenerate. Clean-build
success is insufficient: CI must report whether each declaration was reused,
re-elaborated, reproved, or regenerated at the declared dependency boundary.

## 11. Product limits and open interface pressures

The proposed artifact is shippable only for the declared Vulkan 1.3/dynamic-
rendering profile. It intentionally has one queue and frame in flight, fixed
format/FIFO presentation, no depth buffer, no antialiasing, no high-DPI policy,
no fullscreen, no accessibility UI, no device/surface recovery, and no runtime
shader compilation. Rotation follows portable monotonic elapsed time at the
specified angular velocity; refresh rate, frame coalescing, and GPU latency may
change sampling but not speed.

One frame in flight, the split acquire/submit/present topology, resize
coalescing, and ownership by a single graphics coordinator are replaceable
implementation choices. Close/Escape behavior, elapsed-time advancement,
the accepted image envelope, resize's logical effect, and failure-versus-user-
success classification are product semantics and remain precious. The product
review must make that classification before accepting a supposedly cheaper
proof. In particular, the present source cannot cancel an already-blocking
Vulkan call: shutdown responsiveness is conditional on settlement of issued
frontiers. Claiming unconditional interactive cancellation would require a new
provider strategy and machine source, not a weakened proof premise.

The spike validates the process boundary in addition to pressuring lower corpus
interfaces:

1. `VerifiedProgram spec` must existentially carry this exact nonprecious
   `processPlan`, its realization proof, the host source, and both device
   sources. None may leak into the stable public index.
2. Artifact connection needs exact embedded-subartifact ranges and an API-use
   theorem tying those bytes to device-program consumption.
3. Obligations need explicit GPU submission, semaphore/fence, acquired-image,
   presentation, and device-loss disposition protocols.
4. The standard process library needs reusable window-input,
   frame-opportunity, acquire, submission, presentation, correlated-response,
   cancellation/drain, and device-loss laws without standardizing this spike's
   topology.
5. Reactive liveness must compose a Win32 input strategy, blocking API strategy,
   scheduler, and GPU completion strategy without asserting unconditional
   termination or cancellation of an uncancellable committed operation.
6. API authoring needs transparent structure/call syntax whose literal expansion
   is line-auditable; otherwise Vulkan boilerplate will overwhelm the semantic
   proof while silently taking assembly authorship away.
7. Process diagnostics must show the process/channel/ownership graph beside the
   exact mapped CFG intervals, so a convenient reactive proof cannot conceal an
   unmodeled callback, API occurrence, or GPU frontier.

Decision 42 settles the presentation rule: inspectability on demand is not
enough. Spike 5's review artifact and every implementation review must print the
fully expanded raw host listing, static data, shader words, imports,
relocations, and artifact layout. Transparent authoring macros remain useful,
but their displayed expansion is part of the evidence under review.


## Exact authored source snapshot

This snapshot is the exact comment-free source maintained under
`Spikes/5_Spinning_Cube/`. Run `./check-spike-sources.ps1 -Spike 5` to check the
normalized cross-view equality and block classifications.

### `Assembly.lean`

<!-- grass-block: authored file=Assembly.lean -->
```lean
import Grass.Assembly.X86
import Grass.Assembly.Spirv
import Spikes.«5_Spinning_Cube».Macros

namespace Grass.Spikes.SpinningCube

def cubeVertex : SpirvModule plan.shaderEnv := spirv_asm {
  OpCapability Shader
  %glsl = OpExtInstImport "GLSL.std.450"
  OpMemoryModel Logical GLSL450
  OpEntryPoint Vertex %main "main" %vertexIndex %positionOut %colorOut
    %push %positionsVar %indicesVar
  OpName %main "main"
  OpDecorate %vertexIndex BuiltIn VertexIndex
  OpDecorate %positionOut BuiltIn Position
  OpDecorate %colorOut Location 0
  OpMemberDecorate %Push 0 Offset 0
  OpMemberDecorate %Push 1 Offset 4
  OpDecorate %Push Block

  %void = OpTypeVoid
  %fn = OpTypeFunction %void
  %bool = OpTypeBool
  %int = OpTypeInt 32 1
  %uint = OpTypeInt 32 0
  %float = OpTypeFloat 32
  %i0=OpConstant %int 0  %i1=OpConstant %int 1
  %i2=OpConstant %int 2  %i3=OpConstant %int 3
  %i4=OpConstant %int 4  %i5=OpConstant %int 5
  %i6=OpConstant %int 6  %i7=OpConstant %int 7
  %u8=OpConstant %uint 8  %u24=OpConstant %uint 24
  %f0=OpConstant %float 0.0  %f1=OpConstant %float 1.0
  %fn1=OpConstant %float -1.0  %f2=OpConstant %float 2.0
  %f3=OpConstant %float 3.0  %f025=OpConstant %float 0.25
  %v3 = OpTypeVector %float 3
  %v4 = OpTypeVector %float 4
  %Push = OpTypeStruct %float %float
  %ptrPush = OpTypePointer PushConstant %Push
  %ptrPushF = OpTypePointer PushConstant %float
  %ptrInI = OpTypePointer Input %int
  %ptrOutV4 = OpTypePointer Output %v4
  %ptrOutV3 = OpTypePointer Output %v3
  %arrPos = OpTypeArray %v3 %u8
  %arrIdx = OpTypeArray %int %u24
  %ptrPrivatePos = OpTypePointer Private %arrPos
  %ptrPrivateIdx = OpTypePointer Private %arrIdx
  %ptrPrivateV3 = OpTypePointer Private %v3
  %ptrPrivateI = OpTypePointer Private %int

  %p0=OpConstantComposite %v3 %fn1 %fn1 %fn1
  %p1=OpConstantComposite %v3 %f1 %fn1 %fn1
  %p2=OpConstantComposite %v3 %f1 %f1 %fn1
  %p3=OpConstantComposite %v3 %fn1 %f1 %fn1
  %p4=OpConstantComposite %v3 %fn1 %fn1 %f1
  %p5=OpConstantComposite %v3 %f1 %fn1 %f1
  %p6=OpConstantComposite %v3 %f1 %f1 %f1
  %p7=OpConstantComposite %v3 %fn1 %f1 %f1
  %bias=OpConstantComposite %v3 %f025 %f025 %f025
  %positions=OpConstantComposite %arrPos %p0 %p1 %p2 %p3 %p4 %p5 %p6 %p7
  %indices=OpConstantComposite %arrIdx
    %i0 %i1 %i1 %i2 %i2 %i3 %i3 %i0
    %i4 %i5 %i5 %i6 %i6 %i7 %i7 %i4
    %i0 %i4 %i1 %i5 %i2 %i6 %i3 %i7
  %vertexIndex = OpVariable %ptrInI Input
  %positionOut = OpVariable %ptrOutV4 Output
  %colorOut = OpVariable %ptrOutV3 Output
  %push = OpVariable %ptrPush PushConstant
  %positionsVar = OpVariable %ptrPrivatePos Private %positions
  %indicesVar = OpVariable %ptrPrivateIdx Private %indices

  %main = OpFunction %void None %fn
  %entry = OpLabel
  %vi = OpLoad %int %vertexIndex
  %ip = OpAccessChain %ptrPrivateI %indicesVar %vi
  %ix = OpLoad %int %ip
  %pp = OpAccessChain %ptrPrivateV3 %positionsVar %ix
  %p = OpLoad %v3 %pp
  %anglePtr = OpAccessChain %ptrPushF %push %i0
  %aspectPtr = OpAccessChain %ptrPushF %push %i1
  %angle = OpLoad %float %anglePtr
  %aspect = OpLoad %float %aspectPtr
  %s = OpExtInst %float %glsl Sin %angle
  %c = OpExtInst %float %glsl Cos %angle
  %x = OpCompositeExtract %float %p 0
  %y = OpCompositeExtract %float %p 1
  %z = OpCompositeExtract %float %p 2
  %cx = OpFMul %float %c %x
  %sz = OpFMul %float %s %z
  %rx = OpFAdd %float %cx %sz
  %sx = OpFMul %float %s %x
  %cz = OpFMul %float %c %z
  %rz0 = OpFSub %float %cz %sx
  %rz = OpFAdd %float %rz0 %f3
  %rxAspect = OpFDiv %float %rx %aspect
  %clipX = OpFDiv %float %rxAspect %rz
  %clipY = OpFDiv %float %y %rz
  %depth0 = OpFSub %float %rz %f1
  %depth = OpFDiv %float %depth0 %rz
  %clip = OpCompositeConstruct %v4 %clipX %clipY %depth %f1
  OpStore %positionOut %clip
  %half = OpVectorTimesScalar %v3 %p %f025
  %color = OpFAdd %v3 %half %bias
  OpStore %colorOut %color
  OpReturn
  OpFunctionEnd
}

def cubeFragment : SpirvModule plan.shaderEnv := spirv_asm {
  OpCapability Shader
  OpMemoryModel Logical GLSL450
  OpEntryPoint Fragment %main "main" %colorIn %colorOut
  OpExecutionMode %main OriginUpperLeft
  OpDecorate %colorIn Location 0
  OpDecorate %colorOut Location 0
  %void=OpTypeVoid
  %fn=OpTypeFunction %void
  %float=OpTypeFloat 32
  %v3=OpTypeVector %float 3
  %v4=OpTypeVector %float 4
  %ptrInV3=OpTypePointer Input %v3
  %ptrOutV4=OpTypePointer Output %v4
  %f1=OpConstant %float 1.0
  %colorIn=OpVariable %ptrInV3 Input
  %colorOut=OpVariable %ptrOutV4 Output
  %main=OpFunction %void None %fn
  %entry=OpLabel
  %rgb=OpLoad %v3 %colorIn
  %r=OpCompositeExtract %float %rgb 0
  %g=OpCompositeExtract %float %rgb 1
  %b=OpCompositeExtract %float %rgb 2
  %rgba=OpCompositeConstruct %v4 %r %g %b %f1
  OpStore %colorOut %rgba
  OpReturn
  OpFunctionEnd
}

def cubeStaticObjects : StaticObjectTable := #[
  .utf16 `className "GrassCube\0",
  .utf16 `title "Grass Vulkan Cube\0",
  .ascii `grass "grass\0",
  .ascii `mainName "main\0",
  .ascii `vkCreateInstanceName "vkCreateInstance\0",
  .ascii `swapchainExtName "VK_KHR_swapchain\0",
  .cstringArray `instanceExts instanceExtensionNames,
  .cstringArray `deviceExts deviceExtensionNames,
  .cstringArray `instanceNames instanceFunctionNames,
  .cstringArray `deviceNames deviceFunctionNames,
  .uint32 `instanceSlotCount instanceFunctionNames.size,
  .uint32 `deviceSlotCount deviceFunctionNames.size,
  .float32 `one 1.0,
  .uint32 `colorFormat VK_FORMAT_B8G8R8A8_UNORM,
  .float64 `angularVelocity 0.6,
  .float64 `tau 6.283185307179586,
  .spirvWords `cubeVertexBytes (Spirv.writeWords cubeVertex),
  .spirvWords `cubeFragmentBytes (Spirv.writeWords cubeFragment)
]

def cubeHost : AsmSource plan :=
  asm_source
    (statics := cubeStaticObjects)
    (constructors := cubeMacroDefinitions)
    (layouts := #[cubeFrameLayout, cubeCallbackFrameLayout]) {
entry: @entry win64_gui_entry
  push rbx
  push rbp
  push rsi
  push rdi
  push r12
  push r13
  push r14
  push r15
  sub rsp, FRAME_SIZE
  xor eax,eax
  lea rdi,[rsp+locals]
  mov ecx,LOCALS_QWORDS
  rep stosq
  win_call GetProcessHeap() -> rax
  test rax,rax
  jz fail_init
  mov qword ptr [processHeap],rax
  win_call GetModuleHandleW(0) -> r12
  test r12,r12
  jz fail_init
  store32 wc.cbSize,SIZEOF_WNDCLASSEXW
  store32 wc.style,CS_HREDRAW|CS_VREDRAW|CS_OWNDC
  store64 wc.lpfnWndProc,&wndproc
  store64 wc.hInstance,r12
  win_call LoadCursorW(0,IDC_ARROW) -> rax
  store64 wc.hCursor,rax
  store64 wc.lpszClassName,&className
  win_call RegisterClassExW(&wc) -> eax
  test ax,ax
  jz fail_init
  mov byte ptr [ownership.classRegistered],1
  win_call CreateWindowExW(0,&className,&title,WS_OVERLAPPEDWINDOW,
      CW_USEDEFAULT,CW_USEDEFAULT,960,720,0,0,r12,&state) -> r13
  test r13,r13
  jz fail_init
  mov byte ptr [state.hwndOwned],1
  win_call ShowWindow(r13,SW_SHOW) -> _
  win_call QueryPerformanceFrequency(&qpcFrequency) -> eax
  test eax,eax
  jz fail_init
  cmp qword ptr [qpcFrequency],0
  jle fail_init
  win_call QueryPerformanceCounter(&qpcEpoch) -> eax
  test eax,eax
  jz fail_init
  mov rax,qword ptr [qpcEpoch]
  mov qword ptr [qpcPrevious],rax
  jmp vk_instance

wndproc: @entry win64_callback(hwnd,msg,wparam,lparam)
  sub rsp,CALLBACK_FRAME_SIZE
  mov qword ptr [rsp+callbackHwnd],rcx
  mov dword ptr [rsp+callbackMessage],edx
  mov qword ptr [rsp+callbackWparam],r8
  mov qword ptr [rsp+callbackLparam],r9
  cmp edx,WM_NCCREATE
  je wp_nccreate
  win_call GetWindowLongPtrW(rcx,GWLP_USERDATA) -> r10
  test r10,r10
  jz wp_default
  mov edx,dword ptr [rsp+callbackMessage]
  mov r8,qword ptr [rsp+callbackWparam]
  mov r9,qword ptr [rsp+callbackLparam]
  cmp edx,WM_CLOSE
  je wp_close
  cmp edx,WM_DESTROY
  je wp_destroyed
  cmp edx,WM_NCDESTROY
  je wp_ncdestroy
  cmp edx,WM_KEYDOWN
  jne wp_size
  cmp r8d,VK_ESCAPE
  je wp_close
wp_size:
  cmp edx,WM_SIZE
  jne wp_default
  mov eax,r9d
  and eax,0xffff
  shr r9d,16
  store32 [r10+CubeWindowState.width],eax
  store32 [r10+CubeWindowState.height],r9d
  mov byte ptr [r10+CubeWindowState.resize],1
  xor eax,eax
  add rsp,CALLBACK_FRAME_SIZE
  ret
wp_nccreate:
  mov r10,qword ptr [r9+CREATESTRUCTW.lpCreateParams]
  test r10,r10
  jz wp_reject_create
  mov qword ptr [rsp+callbackState],r10
  win_call SetWindowLongPtrW(rcx,GWLP_USERDATA,r10) -> _
  mov rcx,qword ptr [rsp+callbackHwnd]
  win_call GetWindowLongPtrW(rcx,GWLP_USERDATA) -> rax
  cmp rax,qword ptr [rsp+callbackState]
  jne wp_reject_create
  mov eax,1
  add rsp,CALLBACK_FRAME_SIZE
  ret
wp_reject_create:
  xor eax,eax
  add rsp,CALLBACK_FRAME_SIZE
  ret
wp_close:
  mov byte ptr [r10+CubeWindowState.exit],1
  xor eax,eax
  add rsp,CALLBACK_FRAME_SIZE
  ret
wp_destroyed:
  mov byte ptr [r10+CubeWindowState.exit],1
  mov byte ptr [r10+CubeWindowState.hwndOwned],0
  xor eax,eax
  add rsp,CALLBACK_FRAME_SIZE
  ret
wp_ncdestroy:
  mov byte ptr [r10+CubeWindowState.hwndOwned],0
  mov rcx,qword ptr [rsp+callbackHwnd]
  win_call SetWindowLongPtrW(rcx,GWLP_USERDATA,0) -> _
  xor eax,eax
  add rsp,CALLBACK_FRAME_SIZE
  ret
wp_default:
  mov rcx,qword ptr [rsp+callbackHwnd]
  mov edx,dword ptr [rsp+callbackMessage]
  mov r8,qword ptr [rsp+callbackWparam]
  mov r9,qword ptr [rsp+callbackLparam]
  win_call DefWindowProcW(rcx,rdx,r8,r9) -> rax
  add rsp,CALLBACK_FRAME_SIZE
  ret

vk_instance:
  init appInfo {sType=APPLICATION_INFO,pApplicationName=&title,
      applicationVersion=1,pEngineName=&grass,engineVersion=1,
      apiVersion=VK_API_VERSION_1_3}
  init instanceCI {sType=INSTANCE_CREATE_INFO,pApplicationInfo=&appInfo,
      enabledExtensionCount=2,ppEnabledExtensionNames=&instanceExts}
  xor ecx,ecx
  lea rdx,[vkCreateInstanceName]
  call qword ptr [rip+__imp_vkGetInstanceProcAddr]
  test rax,rax
  jz fail_init
  mov [vkCreateInstancePtr],rax
  mov rcx,&instanceCI
  xor edx,edx
  lea r8,[instance]
  call qword ptr [vkCreateInstancePtr]
  test eax,eax
  jnz fail_init
  mov byte ptr [ownership.instanceOwned],1
  resolve_instance_functions_or_fail instance, instanceDispatch
  vk_call vkCreateWin32SurfaceKHR(instance,
      {sType=WIN32_SURFACE_CREATE_INFO_KHR,hinstance=r12,hwnd=r13},0,&surface)
  test eax,eax
  jnz fail_init
  mov byte ptr [ownership.surfaceOwned],1

select_device:
  vk_call vkEnumeratePhysicalDevices(instance,&count,0)
  test eax,eax
  jnz fail_init
  test count,count
  jz fail_init
  checked_alloc count*8 -> devices
  jz fail_init
  vk_call vkEnumeratePhysicalDevices(instance,&count,devices)
  test eax,eax
  jnz fail_init
  enumerate_and_select_literal_loop devices,count -> physical,qfamily
  test physical,physical
  jz fail_init

create_device:
  init queueCI {sType=DEVICE_QUEUE_CREATE_INFO,queueFamilyIndex=qfamily,
      queueCount=1,pQueuePriorities=&one}
  init features13 {sType=PHYSICAL_DEVICE_VULKAN_1_3_FEATURES,
      dynamicRendering=1,synchronization2=1}
  init deviceCI {sType=DEVICE_CREATE_INFO,pNext=&features13,
      queueCreateInfoCount=1,pQueueCreateInfos=&queueCI,
      enabledExtensionCount=1,ppEnabledExtensionNames=&deviceExts}
  vk_call vkCreateDevice(physical,&deviceCI,0,&device)
  test eax,eax
  jnz fail_init
  mov byte ptr [ownership.deviceOwned],1
  mov rcx,[device]
  mov rdx,[deviceNames]
  call qword ptr [rip+__imp_vkGetDeviceProcAddr]
  test rax,rax
  jz provider_violation @violation_edge(.missingRequiredDeviceDestroy)
  mov [vkDestroyDevicePtr],rax
  mov byte ptr [ownership.deviceDestroyReady],1
  resolve_device_functions_or_fail device,deviceDispatch
  vk_call vkGetDeviceQueue(device,qfamily,0,&queue)
  jmp create_fixed

create_fixed:
  vk_call vkCreateCommandPool(device,
    {sType=COMMAND_POOL_CREATE_INFO,flags=RESET_COMMAND_BUFFER_BIT,
     queueFamilyIndex=qfamily},0,&commandPool)
     test eax,eax
     jnz fail_init
  mov byte ptr [ownership.commandPoolOwned],1
  vk_call vkAllocateCommandBuffers(device,
    {sType=COMMAND_BUFFER_ALLOCATE_INFO,commandPool=commandPool,
     level=PRIMARY,commandBufferCount=1},&cmd)
     test eax,eax
     jnz fail_init
  vk_call vkCreateSemaphore(device,{sType=SEMAPHORE_CREATE_INFO},0,&imageAvail)
  test eax,eax
  jnz fail_init
  mov byte ptr [ownership.imageAvailOwned],1
  vk_call vkCreateSemaphore(device,{sType=SEMAPHORE_CREATE_INFO},0,&renderDone)
  test eax,eax
  jnz fail_init
  mov byte ptr [ownership.renderDoneOwned],1
  vk_call vkCreateFence(device,{sType=FENCE_CREATE_INFO,flags=SIGNALED_BIT},0,&fence)
  test eax,eax
  jnz fail_init
  mov byte ptr [ownership.fenceOwned],1
  vk_call vkCreateShaderModule(device,{sType=SHADER_MODULE_CREATE_INFO,
    codeSize=cubeVertexBytes.size,pCode=&cubeVertexBytes},0,&vertModule)
  test eax,eax
  jnz fail_init
  mov byte ptr [ownership.vertModuleOwned],1
  vk_call vkCreateShaderModule(device,{sType=SHADER_MODULE_CREATE_INFO,
    codeSize=cubeFragmentBytes.size,pCode=&cubeFragmentBytes},0,&fragModule)
  test eax,eax
  jnz fail_init
  mov byte ptr [ownership.fragModuleOwned],1
  vk_call vkCreatePipelineLayout(device,{sType=PIPELINE_LAYOUT_CREATE_INFO,
    pushConstantRangeCount=1,pPushConstantRanges=&{stageFlags=VERTEX_BIT,
    offset=0,size=8}},0,&pipelineLayout)
    test eax,eax
    jnz fail_init
  mov byte ptr [ownership.pipelineLayoutOwned],1
  jmp recreate

recreate: @invariant fixed_objects_owned_and_no_swapchain_work
  mov eax,dword ptr [state.width]
  test eax,eax
  jz minimized_wait
  mov eax,dword ptr [state.height]
  test eax,eax
  jz minimized_wait
  vk_call vkDeviceWaitIdle(device)
  cmp eax,VK_SUCCESS
  jne fail_runtime
  destroy_swapchain_views_pipeline_if_owned
  vk_call vkGetPhysicalDeviceSurfaceCapabilitiesKHR(physical,surface,&caps)
  test eax,eax
  jnz surface_result
  test caps.supportedUsageFlags,VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT
  jz fail_runtime
  test caps.supportedCompositeAlpha,VK_COMPOSITE_ALPHA_OPAQUE_BIT_KHR
  jz fail_runtime
  vk_call vkGetPhysicalDeviceSurfaceFormatsKHR(physical,surface,&fmtCount,0)
  test eax,eax
  jnz surface_result
  checked_alloc fmtCount*SIZEOF_FORMAT -> formats
  jz fail_runtime
  vk_call vkGetPhysicalDeviceSurfaceFormatsKHR(physical,surface,&fmtCount,formats)
  test eax,eax
  jnz surface_result
  select_required_format_or_fail formats,fmtCount -> surfaceFormat
  compute_extent_and_count caps,width,height -> extent,imageCount
  init swapCI {sType=SWAPCHAIN_CREATE_INFO_KHR,surface=surface,
    minImageCount=imageCount,imageFormat=B8G8R8A8_UNORM,
    imageColorSpace=SRGB_NONLINEAR_KHR,imageExtent=extent,imageArrayLayers=1,
    imageUsage=COLOR_ATTACHMENT_BIT,imageSharingMode=EXCLUSIVE,
    preTransform=caps.currentTransform,compositeAlpha=OPAQUE_BIT_KHR,
    presentMode=FIFO_KHR,clipped=1,oldSwapchain=oldSwapchain}
  vk_call vkCreateSwapchainKHR(device,&swapCI,0,&newSwapchain)
  test eax,eax
  jnz surface_result
  mov byte ptr [ownership.newSwapchainOwned],1
  destroy_old_swapchain_after_new_created
  vk_call vkGetSwapchainImagesKHR(device,swapchain,&imageCount,0)
  test eax,eax
  jnz surface_result
  checked_alloc imageCount*8 -> images
  jz fail_runtime
  checked_alloc imageCount*8 -> views
  jz fail_runtime
  checked_alloc imageCount -> imageInitialized
  jz fail_runtime
  mov rdi,[imageInitialized]
  xor eax,eax
  mov ecx,[imageCount]
  rep stosb
  mov dword ptr [initializedViewCount],0
  mov dword ptr [viewIndex],0
  vk_call vkGetSwapchainImagesKHR(device,swapchain,&imageCount,images)
  test eax,eax
  jnz surface_result
create_view_loop: @measure imageCount-viewIndex
  cmp viewIndex,imageCount
  je create_pipeline
  vk_call vkCreateImageView(device,{sType=IMAGE_VIEW_CREATE_INFO,
    image=images[viewIndex],viewType=TYPE_2D,format=B8G8R8A8_UNORM,
    components={IDENTITY,IDENTITY,IDENTITY,IDENTITY},subresourceRange=
    {aspectMask=COLOR_BIT,baseMipLevel=0,levelCount=1,
     baseArrayLayer=0,layerCount=1}},0,&views[viewIndex])
  test eax,eax
  jnz fail_runtime
  inc dword ptr [initializedViewCount]
  inc viewIndex
  jmp create_view_loop
create_pipeline:
  init shaderStages[0] {sType=PIPELINE_SHADER_STAGE_CREATE_INFO,
      stage=VERTEX_BIT,module=vertModule,pName=&mainName}
  init shaderStages[1] {sType=PIPELINE_SHADER_STAGE_CREATE_INFO,
      stage=FRAGMENT_BIT,module=fragModule,pName=&mainName}
  init emptyVertexInput {sType=PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO}
  init lineList {sType=PIPELINE_INPUT_ASSEMBLY_STATE_CREATE_INFO,
      topology=PRIMITIVE_TOPOLOGY_LINE_LIST,primitiveRestartEnable=0}
  init oneDynamicViewport {sType=PIPELINE_VIEWPORT_STATE_CREATE_INFO,
      viewportCount=1,scissorCount=1}
  init lineRaster {sType=PIPELINE_RASTERIZATION_STATE_CREATE_INFO,
      depthClampEnable=0,rasterizerDiscardEnable=0,polygonMode=POLYGON_MODE_FILL,
      cullMode=CULL_MODE_NONE,frontFace=FRONT_FACE_COUNTER_CLOCKWISE,
      depthBiasEnable=0,lineWidth=1.0f}
  init sample1 {sType=PIPELINE_MULTISAMPLE_STATE_CREATE_INFO,
      rasterizationSamples=SAMPLE_COUNT_1_BIT}
  init colorAttachment {blendEnable=0,
      colorWriteMask=R_BIT|G_BIT|B_BIT|A_BIT}
  init opaqueBlend {sType=PIPELINE_COLOR_BLEND_STATE_CREATE_INFO,
      attachmentCount=1,pAttachments=&colorAttachment}
  store32 dynamicStates[0],DYNAMIC_STATE_VIEWPORT
  store32 dynamicStates[1],DYNAMIC_STATE_SCISSOR
  init viewportScissor {sType=PIPELINE_DYNAMIC_STATE_CREATE_INFO,
      dynamicStateCount=2,pDynamicStates=&dynamicStates}
  init pipelineRendering {sType=PIPELINE_RENDERING_CREATE_INFO,
      colorAttachmentCount=1,pColorAttachmentFormats=&colorFormat}
  init graphicsCI {sType=GRAPHICS_PIPELINE_CREATE_INFO,pNext=&pipelineRendering,
      stageCount=2,pStages=&shaderStages,pVertexInputState=&emptyVertexInput,
      pInputAssemblyState=&lineList,pViewportState=&oneDynamicViewport,
      pRasterizationState=&lineRaster,pMultisampleState=&sample1,
      pColorBlendState=&opaqueBlend,pDynamicState=&viewportScissor,
      layout=pipelineLayout,renderPass=0,subpass=0}
  vk_call vkCreateGraphicsPipelines(device,0,1,&graphicsCI,0,&pipeline)
  test eax,eax
  jnz fail_runtime
  mov byte ptr [ownership.pipelineOwned],1
  mov byte ptr [state.resize],0
  jmp event_loop

minimized_wait:
  cmp byte ptr [state.exit],0
  jne clean_exit
  win_call WaitMessage() -> eax
  test eax,eax
  jz fail_runtime
  jmp pump_messages

event_loop: @frontier_or_measure(message_or_frame)
pump_messages:
  win_call PeekMessageW(&msg,0,0,0,PM_REMOVE) -> eax
  test eax,eax
  jz messages_done
  cmp msg.message,WM_QUIT
  je request_exit
  win_call TranslateMessage(&msg) -> _
  win_call DispatchMessageW(&msg) -> _
  jmp pump_messages
request_exit:
  mov byte ptr [state.exit],1
messages_done:
  cmp byte ptr [state.exit],0
  jne clean_exit
  cmp byte ptr [state.resize],0
  jne recreate
  vk_call vkWaitForFences(device,1,&fence,1,UINT64_MAX)
  cmp eax,VK_SUCCESS
  jne device_result
  vk_call vkAcquireNextImageKHR(device,swapchain,UINT64_MAX,imageAvail,0,&imageIndex)
  cmp eax,VK_ERROR_OUT_OF_DATE_KHR
  je recreate
  cmp eax,VK_SUBOPTIMAL_KHR
  je acquired_suboptimal
  cmp eax,VK_SUCCESS
  jne device_result
  mov byte ptr [state.recreateAfterPresent],0
  jmp acquired
acquired_suboptimal:
  mov byte ptr [state.recreateAfterPresent],1
acquired:
  vk_call vkResetFences(device,1,&fence)
  cmp eax,VK_SUCCESS
  jne device_result
  vk_call vkResetCommandBuffer(cmd,0)
  cmp eax,VK_SUCCESS
  jne device_result
  vk_call vkBeginCommandBuffer(cmd,{sType=COMMAND_BUFFER_BEGIN_INFO,
      flags=ONE_TIME_SUBMIT_BIT})
      cmp eax,VK_SUCCESS
      jne device_result
  mov ecx,dword ptr [imageIndex]
  init barrier {sType=IMAGE_MEMORY_BARRIER_2,
      dstStageMask=COLOR_ATTACHMENT_OUTPUT,dstAccessMask=COLOR_ATTACHMENT_WRITE,
      newLayout=COLOR_ATTACHMENT_OPTIMAL,image=images[rcx],
      subresourceRange={aspectMask=COLOR_BIT,baseMipLevel=0,levelCount=1,
      baseArrayLayer=0,layerCount=1}}
  cmp byte ptr [imageInitialized+rcx],0
  je acquired_first_layout
  store32 barrier.oldLayout,PRESENT_SRC_KHR
  jmp acquired_layout_ready
acquired_first_layout:
  store32 barrier.oldLayout,UNDEFINED
  mov byte ptr [imageInitialized+rcx],1
acquired_layout_ready:
  init dependencyInfo {sType=DEPENDENCY_INFO,imageMemoryBarrierCount=1,
      pImageMemoryBarriers=&barrier}
  vk_call vkCmdPipelineBarrier2(cmd,&dependencyInfo)
  mov ecx,dword ptr [imageIndex]
  init renderingAttachment {sType=RENDERING_ATTACHMENT_INFO,
      imageView=views[rcx],imageLayout=COLOR_ATTACHMENT_OPTIMAL,
      loadOp=CLEAR,storeOp=STORE,clearValue={0.02,0.02,0.04,1}}
  init rendering {sType=RENDERING_INFO,renderArea={0,extent},layerCount=1,
      colorAttachmentCount=1,pColorAttachments=&renderingAttachment}
  vk_call vkCmdBeginRendering(cmd,&rendering)
  vk_call vkCmdBindPipeline(cmd,GRAPHICS,pipeline)
  init viewport {width=float(extent.width),height=float(extent.height),maxDepth=1}
  init scissor {extent=extent}
  vk_call vkCmdSetViewport(cmd,0,1,&viewport)
  vk_call vkCmdSetScissor(cmd,0,1,&scissor)
  win_call QueryPerformanceCounter(&qpcNow) -> eax
  test eax,eax
  jz fail_runtime
  mov rax,qword ptr [qpcNow]
  cmp rax,qword ptr [qpcPrevious]
  jl clock_violation @violation_edge(.monotonicClockRegressed)
  mov qword ptr [qpcPrevious],rax
  sub rax,qword ptr [qpcEpoch]
  jo clock_violation @violation_edge(.monotonicClockRangeExceeded)
  cvtsi2sd xmm1,rax
  cvtsi2sd xmm2,qword ptr [qpcFrequency]
  divsd xmm1,xmm2
  mulsd xmm1,qword ptr [angularVelocity]
  movapd xmm0,xmm1
  movapd xmm3,xmm0
  divsd xmm3,qword ptr [tau]
  roundsd xmm3,xmm3,1
  mulsd xmm3,qword ptr [tau]
  subsd xmm0,xmm3
  cvtsd2ss xmm0,xmm0
  cvtsi2ss xmm1,extent.width
  cvtsi2ss xmm2,extent.height
  divss xmm1,xmm2
  store32 push.angle,xmm0
  store32 push.aspect,xmm1
  vk_call vkCmdPushConstants(cmd,pipelineLayout,VERTEX_BIT,0,8,&push)
  vk_call vkCmdDraw(cmd,24,1,0,0)
  vk_call vkCmdEndRendering(cmd)
  mov ecx,dword ptr [imageIndex]
  init barrier {sType=IMAGE_MEMORY_BARRIER_2,
      srcStageMask=COLOR_ATTACHMENT_OUTPUT,srcAccessMask=COLOR_ATTACHMENT_WRITE,
      oldLayout=COLOR_ATTACHMENT_OPTIMAL,newLayout=PRESENT_SRC_KHR,
      image=images[rcx],subresourceRange={aspectMask=COLOR_BIT,baseMipLevel=0,
      levelCount=1,baseArrayLayer=0,layerCount=1}}
  vk_call vkCmdPipelineBarrier2(cmd,&dependencyInfo)
  vk_call vkEndCommandBuffer(cmd)
  cmp eax,VK_SUCCESS
  jne device_result
  init waitSemaphoreInfo {sType=SEMAPHORE_SUBMIT_INFO,semaphore=imageAvail,
      stageMask=COLOR_ATTACHMENT_OUTPUT}
  init commandBufferInfo {sType=COMMAND_BUFFER_SUBMIT_INFO,commandBuffer=cmd}
  init signalSemaphoreInfo {sType=SEMAPHORE_SUBMIT_INFO,semaphore=renderDone,
      stageMask=ALL_GRAPHICS}
  init submit {sType=SUBMIT_INFO_2,waitSemaphoreInfoCount=1,
      pWaitSemaphoreInfos=&waitSemaphoreInfo,commandBufferInfoCount=1,
      pCommandBufferInfos=&commandBufferInfo,signalSemaphoreInfoCount=1,
      pSignalSemaphoreInfos=&signalSemaphoreInfo}
  vk_call vkQueueSubmit2(queue,1,&submit,fence)
  cmp eax,VK_SUCCESS
  jne device_result
  init present {sType=PRESENT_INFO_KHR,waitSemaphoreCount=1,
      pWaitSemaphores=&renderDone,swapchainCount=1,pSwapchains=&swapchain,
      pImageIndices=&imageIndex}
  vk_call vkQueuePresentKHR(queue,&present)
  cmp eax,VK_ERROR_OUT_OF_DATE_KHR
  je recreate
  cmp eax,VK_SUBOPTIMAL_KHR
  je recreate
  cmp eax,VK_SUCCESS
  jne device_result
  cmp byte ptr [state.recreateAfterPresent],0
  jne recreate
  jmp event_loop

fail_runtime_free_formats:
  free formats
  jmp fail_runtime

surface_result:
  cmp eax,VK_ERROR_SURFACE_LOST_KHR
  je fail_surface
  cmp eax,VK_ERROR_OUT_OF_DATE_KHR
  je recreate
  jmp fail_runtime
device_result:
  cmp eax,VK_ERROR_DEVICE_LOST
  je fail_device
  cmp eax,VK_ERROR_SURFACE_LOST_KHR
  je fail_surface
  jmp fail_runtime

clean_exit: mov ebx,0
jmp cleanup
fail_init: mov ebx,1
jmp cleanup
fail_runtime: mov ebx,2
jmp cleanup
fail_surface: mov ebx,3
mov byte ptr [ownership.surfaceLost],1
jmp cleanup
fail_device: mov ebx,4
mov byte ptr [ownership.deviceLost],1
jmp cleanup
clock_violation:
  ud2 @containment_tail(.monotonicClockRegressed)
provider_violation:
  ud2 @containment_tail(.externalProviderContractViolation)

cleanup: @placement [status := ebx]
         @invariant reverse_dependency_ledger
  reverse_cleanup
  add rsp,FRAME_SIZE
  pop r15
  pop r14
  pop r13
  pop r12
  pop rdi
  pop rsi
  pop rbp
  pop rbx
  mov ecx,ebx
  call qword ptr [rip+__imp_ExitProcess]
  ud2
}

theorem vertexCorrect :
    AssemblyRefinesImplementation
      vertexShaderScope VertexSpirvRepresentation vertexModel cubeVertex := by
  verify_spirv

theorem fragmentCorrect :
    AssemblyRefinesImplementation
      fragmentShaderScope FragmentSpirvRepresentation fragmentModel cubeFragment := by
  verify_spirv

theorem hostImplementsDriver :
    HostAssemblyImplements
      stagedProcessRealization
      plan cubeHost := by
  verify_asm

end Grass.Spikes.SpinningCube
```

### `Layout.lean`

<!-- grass-block: authored file=Layout.lean -->
```lean
import Spikes.«5_Spinning_Cube».Process

namespace Grass.Spikes.SpinningCube

def instanceExtensionNames : Vec CString := #[
  "VK_KHR_surface",
  "VK_KHR_win32_surface"
]

def deviceExtensionNames : Vec CString := #["VK_KHR_swapchain"]

def instanceFunctionNames : Vec CString := #[
  "vkDestroyInstance",
  "vkCreateWin32SurfaceKHR",
  "vkDestroySurfaceKHR",
  "vkEnumeratePhysicalDevices",
  "vkGetPhysicalDeviceProperties2",
  "vkGetPhysicalDeviceFeatures2",
  "vkEnumerateDeviceExtensionProperties",
  "vkGetPhysicalDeviceQueueFamilyProperties2",
  "vkGetPhysicalDeviceSurfaceSupportKHR",
  "vkGetPhysicalDeviceSurfaceCapabilitiesKHR",
  "vkGetPhysicalDeviceSurfaceFormatsKHR",
  "vkCreateDevice"
]

def deviceFunctionNames : Vec CString := #[
  "vkDestroyDevice",
  "vkGetDeviceQueue",
  "vkCreateCommandPool",
  "vkDestroyCommandPool",
  "vkAllocateCommandBuffers",
  "vkCreateSemaphore",
  "vkDestroySemaphore",
  "vkCreateFence",
  "vkDestroyFence",
  "vkCreateShaderModule",
  "vkDestroyShaderModule",
  "vkCreatePipelineLayout",
  "vkDestroyPipelineLayout",
  "vkCreateSwapchainKHR",
  "vkDestroySwapchainKHR",
  "vkGetSwapchainImagesKHR",
  "vkCreateImageView",
  "vkDestroyImageView",
  "vkCreateGraphicsPipelines",
  "vkDestroyPipeline",
  "vkDeviceWaitIdle",
  "vkWaitForFences",
  "vkAcquireNextImageKHR",
  "vkResetFences",
  "vkResetCommandBuffer",
  "vkBeginCommandBuffer",
  "vkCmdPipelineBarrier2",
  "vkCmdBeginRendering",
  "vkCmdBindPipeline",
  "vkCmdSetViewport",
  "vkCmdSetScissor",
  "vkCmdPushConstants",
  "vkCmdDraw",
  "vkCmdEndRendering",
  "vkEndCommandBuffer",
  "vkQueueSubmit2",
  "vkQueuePresentKHR"
]

def cubeFrameObjects : Vec StackObjectSpec := #[
  .object `wc .wndClassExW,
  .object `msg .msg,
  .object `state .cubeWindowState,
  .object `qpcFrequency .int64,
  .object `qpcEpoch .int64,
  .object `qpcPrevious .int64,
  .object `qpcNow .int64,
  .object `processHeap .pointer,
  .object `vkCreateInstancePtr .pointer,
  .object `instance .vkInstance,
  .object `surface .vkSurfaceKHR,
  .object `physical .vkPhysicalDevice,
  .object `qfamily .uint32,
  .object `device .vkDevice,
  .object `queue .vkQueue,
  .object `commandPool .vkCommandPool,
  .object `cmd .vkCommandBuffer,
  .object `imageAvail .vkSemaphore,
  .object `renderDone .vkSemaphore,
  .object `fence .vkFence,
  .object `vertModule .vkShaderModule,
  .object `fragModule .vkShaderModule,
  .object `pipelineLayout .vkPipelineLayout,
  .object `pipeline .vkPipeline,
  .object `swapchain .vkSwapchainKHR,
  .object `oldSwapchain .vkSwapchainKHR,
  .object `newSwapchain .vkSwapchainKHR,
  .object `count .uint32,
  .object `deviceCount .uint32,
  .object `devices .pointer,
  .object `extCount .uint32,
  .object `extProps .pointer,
  .object `queueCount .uint32,
  .object `queueProps .pointer,
  .object `supported .vkBool32,
  .object `fmtCount .uint32,
  .object `formats .pointer,
  .object `surfaceFormat .vkSurfaceFormatKHR,
  .object `imageCount .uint32,
  .object `images .pointer,
  .object `views .pointer,
  .object `imageInitialized .pointer,
  .object `initializedViewCount .uint32,
  .object `viewIndex .uint32,
  .object `imageIndex .uint32,
  .object `appInfo .vkApplicationInfo,
  .object `instanceCI .vkInstanceCreateInfo,
  .object `properties2 .vkPhysicalDeviceProperties2,
  .object `queueCI .vkDeviceQueueCreateInfo,
  .object `features2 .vkPhysicalDeviceFeatures2,
  .object `features13 .vkPhysicalDeviceVulkan13Features,
  .object `deviceCI .vkDeviceCreateInfo,
  .object `win32SurfaceCI .vkWin32SurfaceCreateInfoKHR,
  .object `commandPoolCI .vkCommandPoolCreateInfo,
  .object `commandBufferAI .vkCommandBufferAllocateInfo,
  .object `semaphoreCI .vkSemaphoreCreateInfo,
  .object `fenceCI .vkFenceCreateInfo,
  .object `vertexShaderCI .vkShaderModuleCreateInfo,
  .object `fragmentShaderCI .vkShaderModuleCreateInfo,
  .object `pipelineLayoutCI .vkPipelineLayoutCreateInfo,
  .object `pushConstantRange .vkPushConstantRange,
  .object `caps .vkSurfaceCapabilitiesKHR,
  .object `extent .vkExtent2D,
  .object `swapCI .vkSwapchainCreateInfoKHR,
  .object `pipelineRendering .vkPipelineRenderingCreateInfo,
  .object `graphicsCI .vkGraphicsPipelineCreateInfo,
  .object `imageViewCI .vkImageViewCreateInfo,
  .object `commandBufferBI .vkCommandBufferBeginInfo,
  .object `shaderStages (.array 2 .vkPipelineShaderStageCreateInfo),
  .object `emptyVertexInput .vkPipelineVertexInputStateCreateInfo,
  .object `lineList .vkPipelineInputAssemblyStateCreateInfo,
  .object `oneDynamicViewport .vkPipelineViewportStateCreateInfo,
  .object `lineRaster .vkPipelineRasterizationStateCreateInfo,
  .object `sample1 .vkPipelineMultisampleStateCreateInfo,
  .object `colorAttachment .vkPipelineColorBlendAttachmentState,
  .object `opaqueBlend .vkPipelineColorBlendStateCreateInfo,
  .object `dynamicStates (.array 2 .vkDynamicState),
  .object `viewportScissor .vkPipelineDynamicStateCreateInfo,
  .object `push .cubePushConstants,
  .object `barrier .vkImageMemoryBarrier2,
  .object `dependencyInfo .vkDependencyInfo,
  .object `rendering .vkRenderingInfo,
  .object `renderingAttachment .vkRenderingAttachmentInfo,
  .object `viewport .vkViewport,
  .object `scissor .vkRect2D,
  .object `submit .vkSubmitInfo2,
  .object `waitSemaphoreInfo .vkSemaphoreSubmitInfo,
  .object `signalSemaphoreInfo .vkSemaphoreSubmitInfo,
  .object `commandBufferInfo .vkCommandBufferSubmitInfo,
  .object `present .vkPresentInfoKHR,
  .object `instanceDispatch (.array instanceFunctionNames.size .pointer),
  .object `deviceDispatch (.array deviceFunctionNames.size .pointer),
  .object `deviceDispatchCandidate (.array deviceFunctionNames.size .pointer),
  .object `vkDestroyDevicePtr .pointer,
  .object `ownership .cubeOwnershipLedger,
  .outgoingCallArea,
  .parallelMoveSpill
]

def cubeCallbackFrameObjects : Vec StackObjectSpec := #[
  .object `callbackHwnd .pointer,
  .object `callbackMessage .uint32,
  .object `callbackWparam .uint64,
  .object `callbackLparam .int64,
  .object `callbackState .pointer,
  .outgoingCallArea,
  .parallelMoveSpill
]

def cubeFrameLayout : StackFrameLayout :=
  StackFrameLayout.packWin64 cubeFrameObjects

def cubeCallbackFrameLayout : StackFrameLayout :=
  StackFrameLayout.packWin64 cubeCallbackFrameObjects

end Grass.Spikes.SpinningCube
```

### `Macros.lean`

<!-- grass-block: authored file=Macros.lean -->
```lean
import Spikes.«5_Spinning_Cube».Layout

namespace Grass.Spikes.SpinningCube

def win64ArgLocation : Nat → CallLocation
  | 0 => .register .rcx
  | 1 => .register .rdx
  | 2 => .register .r8
  | 3 => .register .r9
  | n + 4 => .stack (32 + 8 * n)

def expandArguments (arguments : Vec Operand) : Vec RawInstruction :=
  ParallelMove.expand
    (arguments.mapIdx fun index argument =>
      (argument, win64ArgLocation index))

def expandCall (target : CallTarget) (arguments : Vec Operand)
    (result : Option Register) : Vec RawInstruction :=
  expandArguments arguments ++
  #[match target with
    | .iat symbol => .callMem (.ripRelative (iatSymbol symbol))
    | .dispatch base slot => .callMem (.baseDisplacement base slot)] ++
  match result with
  | none => #[]
  | some .rax => #[]
  | some destination => #[.mov destination .rax]

def expandZeroInitializedStructure
    (layout : ProvedStructLayout) (address : Address)
    (fields : Vec FieldInitializer) : Vec RawInstruction :=
  #[.xor .eax .eax,
    .lea .rdi address,
    .mov .ecx (.immediate (layout.size / 8)),
    .repStosq] ++
  fields.map fun field =>
    .movWidth field.layout.width (address + field.layout.offset) field.value

def expandLoad (destinations : Vec Register) (sources : Vec Address) :
    Vec RawInstruction :=
  Vec.zipWith (fun destination source => .mov destination (.memory source))
    destinations sources

def expandUnsignedClamp
    (value low high : Operand) (destination : Address) : Vec RawInstruction := #[
  .mov .eax value,
  .cmp .eax low,
  .cmovb .eax low,
  .cmp .eax high,
  .cmova .eax high,
  .mov32 destination .eax
]

def expandConditionalDestroy
    (tag : Address) (arguments : Vec Operand) (target : CallTarget) :
    Vec RawInstruction :=
  RawInstructionBuilder.withFreshLabel `destroy_done fun done =>
    #[.cmp8 tag 0, .je (.label done)] ++
    expandCall target arguments none ++
    #[.mov8 tag 0, .label done]

def exactCStringScanBody : TransparentAsmFragment plan := asm_fragment {
  xor ebx,ebx
cstr_record_head: @measure recordCount-rbx
  cmp ebx,recordCount
  je cstr_not_found
  lea rsi,[records+rbx*recordStride+recordNameOffset]
  mov rdi,needle
  xor ecx,ecx
cstr_char_head: @measure VK_MAX_EXTENSION_NAME_SIZE-rcx
  cmp ecx,VK_MAX_EXTENSION_NAME_SIZE
  je cstr_next_record
  mov al,[rsi+rcx]
  cmp al,[rdi+rcx]
  jne cstr_next_record
  test al,al
  jz cstr_found
  inc ecx
  jmp cstr_char_head
cstr_next_record:
  inc ebx
  jmp cstr_record_head
cstr_not_found:
  mov ebx,-1
cstr_found:
}

def queuePropertyInitializationBody : TransparentAsmFragment plan := asm_fragment {
  xor ebx,ebx
queue_record_head: @measure queueCount-rbx
  cmp ebx,[queueCount]
  je queue_record_done
  lea rdi,[queueProps+rbx*QSIZE]
  xor eax,eax
  mov ecx,QSIZE/8
  rep stosq
  mov dword ptr [queueProps+rbx*QSIZE+sType],PHYSICAL_DEVICE_QUEUE_FAMILY_PROPERTIES_2
  inc ebx
  jmp queue_record_head
queue_record_done:
}

def checkedHeapAllocationBody : TransparentAsmFragment plan := asm_fragment {
  mov pointer,0
  mov byte ptr [tag],0
  mov rax,count
  mov rcx,stride
  mul rcx
  test rdx,rdx
  jnz allocation_failed
  test count,count
  jz allocation_failed
  test rax,rax
  jz allocation_failed
  mov r8,rax
  mov rcx,[processHeap]
  xor edx,edx
  call qword ptr [rip+__imp_HeapAlloc]
  test rax,rax
  jz allocation_failed
  mov pointer,rax
  mov byte ptr [tag],1
  mov eax,1
  jmp allocation_done
allocation_failed:
  xor eax,eax
allocation_done:
  test eax,eax
}

def checkedHeapReleaseBody : TransparentAsmFragment plan := asm_fragment {
free_head:
  cmp byte ptr [tag],0
  je free_done
  mov rcx,[processHeap]
  xor edx,edx
  mov r8,pointer
  call qword ptr [rip+__imp_HeapFree]
  test eax,eax
  jz provider_violation @violation_edge(.ownedHeapFreeRejected)
  mov pointer,0
  mov byte ptr [tag],0
free_done:
}

def instanceDispatchResolutionBody : TransparentAsmFragment plan := asm_fragment {
resolve_i_init:
  xor r14d,r14d
resolve_i_head: @measure instanceSlotCount-r14
  cmp r14d,instanceSlotCount
  je resolve_i_seal
  mov rcx,[instance]
  mov rdx,[instanceNames+r14*8]
  call qword ptr [rip+__imp_vkGetInstanceProcAddr]
  test rax,rax
  jz fail_init
  mov [instanceDispatch+r14*8],rax
  inc r14d
  jmp resolve_i_head
resolve_i_seal:
  @ghost seal_read_only(instanceDispatch)
}

def deviceDispatchResolutionBody : TransparentAsmFragment plan := asm_fragment {
resolve_d_init:
  xor r14d,r14d
resolve_d_head: @measure deviceSlotCount-r14
  cmp r14d,deviceSlotCount
  je resolve_d_seal
  mov rcx,[device]
  mov rdx,[deviceNames+r14*8]
  call qword ptr [rip+__imp_vkGetDeviceProcAddr]
  test rax,rax
  jz fail_init
  mov [deviceDispatchCandidate+r14*8],rax
  inc r14d
  jmp resolve_d_head
resolve_d_seal:
  lea rsi,[deviceDispatchCandidate]
  lea rdi,[deviceDispatch]
  mov ecx,deviceSlotCount
  rep movsq
  @ghost seal_read_only(deviceDispatch)
  mov byte ptr [ownership.deviceDispatchReady],1
}

def deviceSelectionBody : TransparentAsmFragment plan := asm_fragment {
dev_init:
  xor r14d,r14d
dev_head: @measure deviceCount-r14
  cmp r14d,[deviceCount]
  je fail_init
  mov r15,[devices+r14*8]
  init properties2 {sType=PHYSICAL_DEVICE_PROPERTIES_2}
  vk_call vkGetPhysicalDeviceProperties2(r15,&properties2)
  cmp [properties2.properties.apiVersion],VK_API_VERSION_1_3
  jb dev_next
  init features13 {sType=PHYSICAL_DEVICE_VULKAN_1_3_FEATURES}
  init features2 {sType=PHYSICAL_DEVICE_FEATURES_2,pNext=&features13}
  vk_call vkGetPhysicalDeviceFeatures2(r15,&features2)
  cmp [features13.dynamicRendering],0
  je dev_next
  cmp [features13.synchronization2],0
  je dev_next
ext_count:
  vk_call vkEnumerateDeviceExtensionProperties(r15,0,&extCount,0)
  cmp eax,VK_SUCCESS
  jne dev_next
  checked_alloc extCount*SIZEOF_EXTENSION_PROPERTIES -> extProps
  vk_call vkEnumerateDeviceExtensionProperties(r15,0,&extCount,extProps)
  cmp eax,VK_INCOMPLETE
  je ext_retry
  cmp eax,VK_SUCCESS
  jne dev_next_free_ext
  exact_find_c_string extProps,extCount,&swapchainExtName -> ebx
  js dev_next_free_ext
  vk_call vkGetPhysicalDeviceQueueFamilyProperties2(r15,&queueCount,0)
  checked_alloc queueCount*SIZEOF_QUEUE_PROPERTIES_2 -> queueProps
  initialize_queue_property_records queueProps,queueCount
  vk_call vkGetPhysicalDeviceQueueFamilyProperties2(r15,&queueCount,queueProps)
  xor ebx,ebx
queue_head: @measure queueCount-rbx
  cmp ebx,[queueCount]
  je dev_next_free_all
  test [queueProps+rbx*QSIZE+queueFlags],VK_QUEUE_GRAPHICS_BIT
  jz queue_next
  vk_call vkGetPhysicalDeviceSurfaceSupportKHR(r15,ebx,[surface],&supported)
  cmp eax,VK_SUCCESS
  jne dev_next_free_all
  cmp [supported],0
  jne dev_selected
queue_next:
  inc ebx
  jmp queue_head
dev_selected:
  mov [physical],r15
  mov [qfamily],ebx
  free queueProps
  free extProps
  free devices
  jmp create_device
dev_next_free_all:
  free queueProps
dev_next_free_ext:
  free extProps
dev_next:
  inc r14d
  jmp dev_head
ext_retry:
  free extProps
  jmp ext_count
}

def surfaceSelectionBody : TransparentAsmFragment plan := asm_fragment {
fmt_init:
  xor ebx,ebx
fmt_head: @measure fmtCount-rbx
  cmp ebx,[fmtCount]
  je fail_runtime_free_formats
  cmp [formats+rbx*FSIZE+format],VK_FORMAT_B8G8R8A8_UNORM
  jne fmt_next
  cmp [formats+rbx*FSIZE+colorSpace],VK_COLOR_SPACE_SRGB_NONLINEAR_KHR
  je fmt_found
fmt_next:
  inc ebx
  jmp fmt_head
fmt_found:
  mov rax,[formats+rbx*FSIZE]
  mov [surfaceFormat],rax
  free formats
}

def expandExtentAndCount
    (caps width height extent imageCount : AddressOperand) :
    TransparentAsmFragment plan := asm_fragment {
  cmp [caps.currentExtent.width],UINT32_MAX
  jne extent_fixed
  clamp_u32 width,[caps.min.width],[caps.max.width] -> [extent.width]
  clamp_u32 height,[caps.min.height],[caps.max.height] -> [extent.height]
  jmp extent_done
extent_fixed:
  mov rax,[caps.currentExtent]
  mov [extent],rax
extent_done:
  cmp [extent.width],0
  je minimized_wait
  cmp [extent.height],0
  je minimized_wait
  mov eax,[caps.minImageCount]
  cmp eax,UINT32_MAX
  je fail_runtime
  inc eax
  mov ecx,[caps.maxImageCount]
  test ecx,ecx
  jz count_done
  cmp eax,ecx
  cmova eax,ecx
count_done:
  mov [imageCount],eax
}

def swapchainRetirementBody : TransparentAsmFragment plan := asm_fragment {
destroy_old_init:
  mov ecx,[initializedViewCount]
destroy_old_head: @measure ecx
  test ecx,ecx
  jz destroy_old_pipeline
  dec ecx
  vk_call vkDestroyImageView(device,views[rcx],0)
  mov qword ptr [views+rcx*8],0
  jmp destroy_old_head
destroy_old_pipeline:
  cmp byte ptr [ownership.pipelineOwned],0
  je destroy_old_swap
  vk_call vkDestroyPipeline(device,pipeline,0)
  mov byte ptr [ownership.pipelineOwned],0
destroy_old_swap:
  cmp byte ptr [ownership.swapchainOwned],0
  je destroy_old_arrays
  vk_call vkDestroySwapchainKHR(device,swapchain,0)
  mov byte ptr [ownership.swapchainOwned],0
destroy_old_arrays:
  mov dword ptr [initializedViewCount],0
  mov dword ptr [viewIndex],0
  free imageInitialized
  free views
  free images
}

def installNewSwapchainBody : TransparentAsmFragment plan := asm_fragment {
  mov rax,[newSwapchain]
  mov [swapchain],rax
  mov byte ptr [ownership.newSwapchainOwned],0
  mov byte ptr [ownership.swapchainOwned],1
}

def reverseCleanupBody : TransparentAsmFragment plan := asm_fragment {
cleanup_device_wait:
  cmp byte ptr [ownership.deviceDispatchReady],0
  je cleanup_views
  cmp byte ptr [ownership.deviceLost],0
  jne cleanup_views
  vk_call vkDeviceWaitIdle(device)
cleanup_views:
  mov ecx,[initializedViewCount]
cleanup_view_head: @measure ecx
  test ecx,ecx
  jz cleanup_pipeline
  dec ecx
  vk_call vkDestroyImageView(device,views[rcx],0)
  jmp cleanup_view_head
cleanup_pipeline:
  destroy_if_owned ownership.pipelineOwned,vkDestroyPipeline,device,pipeline
  destroy_if_owned ownership.swapchainOwned,vkDestroySwapchainKHR,device,swapchain
  destroy_if_owned ownership.pipelineLayoutOwned,vkDestroyPipelineLayout,device,pipelineLayout
  destroy_if_owned ownership.fragModuleOwned,vkDestroyShaderModule,device,fragModule
  destroy_if_owned ownership.vertModuleOwned,vkDestroyShaderModule,device,vertModule
  destroy_if_owned ownership.fenceOwned,vkDestroyFence,device,fence
  destroy_if_owned ownership.renderDoneOwned,vkDestroySemaphore,device,renderDone
  destroy_if_owned ownership.imageAvailOwned,vkDestroySemaphore,device,imageAvail
  destroy_if_owned ownership.commandPoolOwned,vkDestroyCommandPool,device,commandPool
  cmp byte ptr [ownership.deviceOwned],0
  je cleanup_surface
  cmp byte ptr [ownership.deviceDestroyReady],0
  je provider_violation @violation_edge(.ownedDeviceWithoutDestroyCapability)
  mov rcx,[device]
  xor edx,edx
  call qword ptr [vkDestroyDevicePtr]
  mov byte ptr [ownership.deviceOwned],0
cleanup_surface:
  destroy_if_owned ownership.surfaceOwned,vkDestroySurfaceKHR,instance,surface
  destroy_if_owned ownership.instanceOwned,vkDestroyInstance,instance
  free imageInitialized
  free views
  free images
  free queueProps
  free extProps
  free devices
  cmp byte ptr [state.hwndOwned],0
  je cleanup_class
  win_call DestroyWindow(r13)
cleanup_class:
  cmp byte ptr [ownership.classRegistered],0
  je cleanup_return
  win_call UnregisterClassW(&className,r12)
cleanup_return:
}

def cubeMacroDefinitions : AsmMacroRegistry plan := #[
  .functional `win_call expandCall,
  .functional `vk_call expandCall,
  .functional `init expandZeroInitializedStructure,
  .literal `checked_alloc checkedHeapAllocationBody,
  .literal `free checkedHeapReleaseBody,
  .literal `resolve_instance_functions_or_fail instanceDispatchResolutionBody,
  .literal `resolve_device_functions_or_fail deviceDispatchResolutionBody,
  .literal `enumerate_and_select_literal_loop deviceSelectionBody,
  .literal `select_required_format_or_fail surfaceSelectionBody,
  .functional `compute_extent_and_count expandExtentAndCount,
  .literal `destroy_swapchain_views_pipeline_if_owned swapchainRetirementBody,
  .literal `destroy_old_swapchain_after_new_created installNewSwapchainBody,
  .literal `reverse_cleanup reverseCleanupBody,
  .singleInstruction `store32 .mov32,
  .singleInstruction `store64 .mov64,
  .functional `load expandLoad,
  .functional `clamp_u32 expandUnsignedClamp,
  .literal `exact_find_c_string exactCStringScanBody,
  .literal `initialize_queue_property_records queuePropertyInitializationBody,
  .functional `destroy_if_owned expandConditionalDestroy
]

end Grass.Spikes.SpinningCube
```

### `Process.lean`

<!-- grass-block: authored file=Process.lean -->
```lean
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
```

### `Program.lean`

<!-- grass-block: authored file=Program.lean -->
```lean
import Grass.Emit
import Spikes.«5_Spinning_Cube».Assembly
import Spikes.«5_Spinning_Cube».Process

namespace Grass.Spikes.SpinningCube

def shaders : ShaderSet plan :=
  { vertex := cubeVertex
    fragment := cubeFragment }

def source : MachineSource plan :=
  { host := cubeHost
    devices := shaders }

def sourceConnections : HeterogeneousSourceConnections plan source :=
  machine_connections {
    callback `wndproc =>
      Win32.windowStatePointer
        (installAt := .wmNcCreate)
        (clearAt := .wmNcDestroy)
    shader `vertexShader =>
      Spirv.module cubeVertex
        (entry := `main)
        (staticRange := `cubeVertexBytes)
        (createCall := `vkCreateShaderModule)
        (codeSize := `cubeVertexBytes.size)
        (codePointer := `cubeVertexBytes.address)
        (returnedHandle := `vertModule)
        (pipelineStage := (`shaderStages, 0, VERTEX_BIT))
        (entryName := `mainName)
    shader `fragmentShader =>
      Spirv.module cubeFragment
        (entry := `main)
        (staticRange := `cubeFragmentBytes)
        (createCall := `vkCreateShaderModule)
        (codeSize := `cubeFragmentBytes.size)
        (codePointer := `cubeFragmentBytes.address)
        (returnedHandle := `fragModule)
        (pipelineStage := (`shaderStages, 1, FRAGMENT_BIT))
        (entryName := `mainName)
    pushConstant `rotation => rotationRepresentation
  }

theorem sourceConnectionsCorrect :
    HeterogeneousSourceConnections.Valid sourceConnections := by
  verify_machine_connections
    using_rotation rotationRepresentationCorrect

def cubeVerified : VerifiedProgram spec := by
  verify_assembly plan
    using_process stagedProcessRealization
    using_models vertexModelCorrect fragmentModelCorrect
    using_machine_proofs hostImplementsDriver vertexCorrect fragmentCorrect
    using_connections sourceConnectionsCorrect
    with source

def bytes : ByteArray := emitProgram cubeVerified

end Grass.Spikes.SpinningCube
```

### `Spec.lean`

<!-- grass-block: authored file=Spec.lean -->
```lean
import Grass.Spec.Graphics
import Grass.Spec.Resource

namespace Grass.Spikes.SpinningCube

def resources : GraphicsResourceModel :=
  GraphicsResourceModel.longLivedApplication
    |>.withNoUnboundedGrassOwnedGrowth
    |>.withTerminalDisposition .closeAllOwnedGraphicsObjects

def geometry : WireGeometry := WireGeometry.unitCube

def vertexColors : VertexColoring geometry :=
  VertexColoring.byVertex #[.red, .green, .blue, .yellow,
    .cyan, .magenta, .white, .black]

def angularVelocity : AngularVelocity := .radiansPerSecond (3 / 5)

def scene : InteractiveScene :=
  Scene.spinningWireGeometry geometry vertexColors angularVelocity

structure CubeFrame where
  extent : Nat × Nat
  sampledAt : MonotonicInstant
  angle : Angle
  image : AbstractImage

def rotationAccuracy : ElapsedRotationAccuracy :=
  ElapsedRotationAccuracy.explicit
    (maxAngleError := .radians (1 / 1024))
    (maxSampleTimeError := .milliseconds 1)

def frameProductivity : ProgressFragment :=
  ProgressFragment.conditionalProductivity
    (enabled := [.running, .visible, .nonzeroExtent, .noExitRequested])
    (assumptions := [.frameOpportunitiesContinue, .schedulerFair,
      .platformResponsive, .gpuResponsive])
    (opportunity := .frameOpportunity)
    (eventually := [.frameObservation, .terminalOutcome])

inductive CubeInput
  | close
  | escapeDown
  | resize (width height : Nat)
  | irrelevant

inductive CubeOutcome
  | userExit
  | initializationFailure
  | graphicsFailure
  | surfaceLost

structure CubeObservation where
  inputs : Stream CubeInput
  frames : Stream CubeFrame
  outcome : Option CubeOutcome

def CubeObservation.Accepts (o : CubeObservation) : Prop :=
  FramesApproximateElapsedRotation
      scene.angularVelocity rotationAccuracy o.frames ∧
  NondecreasingFrameSampleTimes o.frames ∧
  (∀ frame ∈ o.frames,
    RasterizesProjectedWireScene scene frame.extent frame.angle frame.image) ∧
  ResizeAffectsProjectionOnly o.inputs o.frames ∧
  UserExitIffRequestedForConformingRuns o.inputs o.outcome ∧
  FailureNeverNormalizesToUserSuccess o.outcome

def sceneFragment : SceneSpec :=
  Graphics.sceneSpec scene

def cubeTraceFragment {R : Type} [ResourceModel R]
    (resources : R) : TraceSpec resources :=
  Graphics.interactiveTraceSpec CubeInput CubeObservation CubeObservation.Accepts

def cubeSuite {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : SpecificationSuite resources :=
  Graphics.interactiveSceneSuite
    resources sceneFragment (cubeTraceFragment resources) rotationAccuracy

def cubeSpec {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (cubeSuite resources)
    |>.acceptInput [.close, .escapeDown, .resize, .irrelevant]
    |>.withFailures .terminateWithoutFalseSuccess
    |>.withProgress (.all #[
      .reactiveUntilUserExit frontiers :=
        [.externalInput, .frameOpportunity, .frameObservation, .terminalOutcome],
      frameProductivity])

theorem cubeSpecCorrect {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : MeetsAllSpecificationTheorems (cubeSpec resources) :=
  Graphics.interactiveSceneSuiteCaptureCorrect
    resources scene CubeObservation.Accepts rotationAccuracy

def spec : SpecProcess resources := cubeSpec resources

end Grass.Spikes.SpinningCube
```
