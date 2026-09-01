import Grass.Process.Sequential
import Spikes.«1_Hello_World».Spec

namespace Grass.Spikes.HelloWorld

def processRealization : ProcessRealization spec :=
  ProcessRealization.standard (Grass.Std.Realizers.lookupExact spec)

end Grass.Spikes.HelloWorld
