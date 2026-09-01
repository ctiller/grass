import Grass.Process.Blend
import Spikes.«5_Spinning_Cube».Process

namespace Grass.Spikes.SpinningCube

def shapedSpec : StagedProcessPresentation spec :=
  StagedProcessPresentation.ofNetwork spec cubeProtocol
    cubeProcessPresentation.denotationExact
    cubeProcessPresentation.requirementsExact

def inputSubsystem : SubsystemRealization shapedSpec .input :=
  SubsystemRealization.fromPlanScope
    processPlanRealizes (CubeProcessScope.input processPlan)
    cube_input_boundary_exact

def animationSubsystem : SubsystemRealization shapedSpec .sceneAnimator :=
  SubsystemRealization.fromPlanScope
    processPlanRealizes (CubeProcessScope.animation processPlan)
    cube_animation_boundary_exact

def graphicsSubsystem : SubsystemRealization shapedSpec .surfacePresenter :=
  SubsystemRealization.fromPlanScope
    processPlanRealizes (CubeProcessScope.graphics processPlan)
    cube_graphics_boundary_exact

def terminationSubsystem : SubsystemRealization shapedSpec .termination :=
  SubsystemRealization.fromPlanScope
    processPlanRealizes (CubeProcessScope.termination processPlan)
    cube_termination_boundary_exact

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

theorem graphicsOnlyNotClosable :
    ¬ EverySchemaRealizedParametrically graphicsOnlyGraph :=
  cube_graphics_only_has_abstract_schemas

theorem graphicsOnlyNotEmittable : ¬ EmittableProcessRealization graphicsOnly :=
  PartialProcessRealization.notEmittable graphicsOnly graphicsOnlyNotClosable

def inputThenGraphicsGraph : BlendedProcessGraph shapedSpec :=
  graphicsOnlyGraph.realize .input inputSubsystem

def graphicsThenInputGraph : BlendedProcessGraph shapedSpec :=
  (BlendedProcessGraph.allAbstract shapedSpec)
    |>.realize .input inputSubsystem
    |>.realize .surfacePresenter graphicsSubsystem

theorem disjointBlendOrderCommutes :
    inputThenGraphicsGraph ≅ᵍ graphicsThenInputGraph :=
  BlendedProcessGraph.realize_commutes
    cube_input_graphics_disjoint
    cube_input_graphics_requirements_compatible

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

def stagedProcessRealization : ProcessRealization spec :=
  completePartial.close
    cube_every_schema_realized_parametrically
    cube_portable_requirements_resources_obligations_coherent

theorem stagedPlanIsExact :
    stagedProcessRealization.plan = processPlan :=
  cube_closed_blend_elaborates_to_exact_plan

theorem unresolvedDescendantRejected :
    ¬ FrontierComplete cube_graphics_with_abstract_child :=
  cube_abstract_child_is_reachable

theorem conflictingProvidersRejected :
    ¬ RequirementDeltasCompatible cube_vulkan_delta cube_metal_delta :=
  cube_vulkan_metal_conflict

theorem changedMultiplicityRejected :
    ¬ BoundaryExact cube_duplicate_frame_boundary cubeProtocolBoundary :=
  cube_duplicate_frame_changes_multiplicity

theorem increasedFluxRejected :
    ¬ BoundaryResourceFluxPreserved cube_unbounded_frame_queue graphicsSubsystem :=
  cube_unbounded_queue_exceeds_boundary

theorem silentDivergenceRejected :
    ¬ ProductiveLocalSimulation cube_silent_spin graphicsSubsystem :=
  cube_silent_spin_has_no_rank_or_frontier

end Grass.Spikes.SpinningCube

namespace Grass.Spikes.EngineBlendFixture

def resources : CompositeResourceModel :=
  CompositeResourceModel.graphicsStorageSimulation

inductive RoleSchema
  | graphics
  | storage
  | simulation

def RoleSchema.Instance : RoleSchema -> Type
  | .graphics => RenderSessionId
  | .storage => StorageSessionId
  | .simulation => SimulationPartitionId

def protocol : ProtocolSpec resources :=
  EngineProtocol.graphicsStorageSimulation
    (roles := RoleSchema)
    (instances := RoleSchema.Instance)

def spec : SpecProcess resources :=
  SpecProcess.fromProtocolSpec protocol

def shaped : StagedProcessPresentation spec :=
  StagedProcessPresentation.ofProtocol spec protocol
    EngineProtocol.denotationExact
    EngineProtocol.requirementsExact

def vulkanGraphics : SubsystemRealization shaped .graphics :=
  Vulkan.refineGraphicsProtocol shaped

def iocpStorage : SubsystemRealization shaped .storage :=
  Win32.IOCP.refineStorageProtocol shaped

def scalarSimulation : SubsystemRealization shaped .simulation :=
  Std.Simulation.refineProtocol shaped

def graphicsOnlyGraph : BlendedProcessGraph shaped :=
  BlendedProcessGraph.allAbstract shaped
    |>.realize .graphics vulkanGraphics

def storageOnlyGraph : BlendedProcessGraph shaped :=
  BlendedProcessGraph.allAbstract shaped
    |>.realize .storage iocpStorage

def graphicsOnly : PartialProcessRealization shaped graphicsOnlyGraph :=
  ProcessRealization.blend graphicsOnlyGraph

def storageOnly : PartialProcessRealization shaped storageOnlyGraph :=
  ProcessRealization.blend storageOnlyGraph

theorem graphicsOnlyNotEmittable : ¬ EmittableProcessRealization graphicsOnly :=
  PartialProcessRealization.notEmittable graphicsOnly engine_graphics_only_incomplete

theorem storageOnlyNotEmittable : ¬ EmittableProcessRealization storageOnly :=
  PartialProcessRealization.notEmittable storageOnly engine_storage_only_incomplete

def graphicsThenStorage : BlendedProcessGraph shaped :=
  graphicsOnlyGraph.realize .storage iocpStorage

def storageThenGraphics : BlendedProcessGraph shaped :=
  storageOnlyGraph.realize .graphics vulkanGraphics

theorem subsystemOrderCommutes :
    graphicsThenStorage ≅ᵍ storageThenGraphics :=
  BlendedProcessGraph.realize_commutes
    engine_graphics_storage_disjoint
    engine_vulkan_iocp_requirements_compatible

def completeGraph : BlendedProcessGraph shaped :=
  graphicsThenStorage.realize .simulation scalarSimulation

def partial : PartialProcessRealization shaped completeGraph :=
  ProcessRealization.blend completeGraph

def realization : ProcessRealization spec :=
  partial.close engine_all_schemas_realized engine_requirements_coherent

theorem conflictingProviderRejected :
    ¬ RequirementDeltasCompatible
      vulkanGraphics.requirements Metal.requirementDelta :=
  engine_vulkan_metal_conflict

theorem abstractStorageDescendantRejected :
    ¬ FrontierComplete engine_iocp_with_abstract_file_provider :=
  engine_abstract_file_provider_reachable

end Grass.Spikes.EngineBlendFixture
