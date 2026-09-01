import Spikes.«4_Web_Server».Projection
import Spikes.«4_Web_Server».Cancellation

namespace Grass.Spikes.WebServer

def platformPlan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64Http2FixedPool projection

end Grass.Spikes.WebServer
