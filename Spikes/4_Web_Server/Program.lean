import Grass.Emit
import Spikes.«4_Web_Server».Bindings

namespace Grass.Spikes.WebServer

def serverVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    using explicit_process serverProcessPlanRealizes
    using_source_closure serverSourceClosureComplete
    using_expansion serverExpansionExact
    using_cancellation serverCfgCancellationRefines
    with serverExpandedSource

def bytes : ByteArray := emitProgram serverVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  serverVerified.sound

end Grass.Spikes.WebServer
