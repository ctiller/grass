import Grass.Platform.Win10.X64
import Spikes.«4_Web_Server».Spec

namespace Grass.Spikes.WebServer

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10Http2PriorKnowledge
    (endpoint := .ipv4Loopback 8080)
    (gracefulShutdownStatus := 0)
    (startupFailureStatus := 1)

end Grass.Spikes.WebServer
