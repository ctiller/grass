import Grass.Std.Graphics.Cube
import Spikes.«5_Spinning_Cube».Spec

namespace Grass.Spikes.SpinningCube

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

end Grass.Spikes.SpinningCube
