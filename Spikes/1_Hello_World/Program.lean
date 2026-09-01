import Grass.Emit
import Spikes.«1_Hello_World».Assembly

namespace Grass.Spikes.HelloWorld

def helloVerified : VerifiedProgram spec := by
  verify_assembly plan with helloSource

def bytes : ByteArray := emitProgram helloVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  helloVerified.sound

end Grass.Spikes.HelloWorld
