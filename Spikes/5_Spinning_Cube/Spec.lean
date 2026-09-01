import Grass.Spec.Graphics
import Grass.Spec.Resource

namespace Grass.Spikes.SpinningCube

def resources : GraphicsResourceModel :=
  GraphicsResourceModel.longLivedApplication
    |>.withNoUnboundedGrassOwnedGrowth
    |>.withTerminalDisposition .closeAllOwnedGraphicsObjects

def scene : InteractiveScene := Scene.spinningColoredWireCube

structure CubeFrame where
  extent : Nat × Nat
  sampledAt : MonotonicInstant
  angle : Angle
  image : AbstractImage
  depicts : RasterizesProjectedCube scene.geometry extent angle image

def rotationAccuracy : ElapsedRotationAccuracy :=
  ElapsedRotationAccuracy.explicit
    (maxAngleError := .radians (1 / 1024))
    (maxSampleTimeError := .milliseconds 1)

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
  (∀ frame ∈ o.frames, frame.depicts) ∧
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
    |>.withProgress (.reactiveUntilUserExit frontiers :=
      [.externalInput, .frameOpportunity, .frameObservation, .terminalOutcome])

theorem cubeSpecCorrect {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : MeetsAllSpecificationTheorems (cubeSpec resources) :=
  Graphics.interactiveSceneSuiteCaptureCorrect
    resources scene CubeObservation.Accepts rotationAccuracy

def spec : SpecProcess resources := cubeSpec resources

end Grass.Spikes.SpinningCube
