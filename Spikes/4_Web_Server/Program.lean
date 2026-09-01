import Grass.Emit
import Spikes.«4_Web_Server».Assembly
import Spikes.«4_Web_Server».Cancellation

namespace Grass.Spikes.WebServer

def serverVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    deriving_constraints_from spec
    using explicit_process serverProcessPlanRealizes
    using_cancellation serverCancellation
    with serverSource

def bytes : ByteArray := emitProgram serverVerified

end Grass.Spikes.WebServer
