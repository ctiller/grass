import Spikes.«3_Gzip».Model
import Spikes.«3_Gzip».Projection
import Spikes.«3_Gzip».Process

namespace Grass.Spikes.Gzip

def platformPlan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64StreamingIO projection

end Grass.Spikes.Gzip
