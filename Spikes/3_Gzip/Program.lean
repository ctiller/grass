import Grass.Emit
import Spikes.«3_Gzip».Assembly

namespace Grass.Spikes.Gzip

def gzipVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    with gzipSource

def bytes : ByteArray := emitProgram gzipVerified

end Grass.Spikes.Gzip
