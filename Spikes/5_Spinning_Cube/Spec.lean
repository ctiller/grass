import Grass.Spec.Graphics
import Spikes.«5_Spinning_Cube».Resource

namespace Grass.Spikes.SpinningCube

def scene : InteractiveScene := Scene.spinningColoredWireCube

structure CubeFrame where
  extent : Nat × Nat
  sampledAt : MonotonicInstant
  angle : Angle
  image : AbstractImage
  depicts : RasterizesProjectedCube scene.geometry extent angle image

def rotationAccuracy : ElapsedRotationAccuracy :=
  Graphics.defaultInteractiveRotationAccuracy

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

inductive CubeRole
  | input
  | sceneAnimator
  | surfacePresenter
  | termination

def cubeProtocol {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : AbstractSpecificationProcessNetwork resources :=
  Graphics.interactivePresentationProtocol
    (roles := CubeRole)
    (resources := resources)
    (scene := scene)
    (accepts := CubeObservation.Accepts)

def cubeSpec {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : Specification resources :=
  Specification.ofProcesses (cubeProtocol resources)
    |>.acceptInput [.close, .escapeDown, .resize]
    |>.withFailures .terminateWithoutFalseSuccess
    |>.withProgress (.reactiveUntilUserExit frontiers :=
      [.windowInput, .frameOpportunity, .demandResult, .commit])

theorem cubeSpecCorrect {R : Type} [ResourceModel R] [InteractiveGraphicsResources R]
    (resources : R) : MeetsAllSpecificationTheorems (cubeSpec resources) :=
  Graphics.interactivePresentationProtocolCorrect
    resources scene CubeObservation.Accepts rotationAccuracy

def spec : Specification resources := cubeSpec resources

end Grass.Spikes.SpinningCube
