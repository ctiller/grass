import Spikes.«2_Sort».Model
import Spikes.«2_Sort».Projection
import Spikes.«2_Sort».Process

namespace Grass.Spikes.Sort

def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64StandardByteSort projection

end Grass.Spikes.Sort
