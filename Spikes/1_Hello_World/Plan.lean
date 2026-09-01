import Spikes.«1_Hello_World».Projection
import Spikes.«1_Hello_World».Process

namespace Grass.Spikes.HelloWorld

def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64SynchronousStdoutOnly projection

end Grass.Spikes.HelloWorld
