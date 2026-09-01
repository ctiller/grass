import Grass.Emit
import Spikes.«3_Gzip».Assembly

namespace Grass.Spikes.Gzip

def gzipVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    deriving_standard_process_from spec
    using_component gzipImplementationBinding
    with gzipSource

def bytes : ByteArray := emitProgram gzipVerified

end Grass.Spikes.Gzip
