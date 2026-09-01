import Spikes.«5_Spinning_Cube».Model
import Spikes.«5_Spinning_Cube».Projection
import Spikes.«5_Spinning_Cube».Process

namespace Grass.Spikes.SpinningCube

def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64Vulkan13Spirv15 projection

end Grass.Spikes.SpinningCube
