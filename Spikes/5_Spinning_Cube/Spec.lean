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
