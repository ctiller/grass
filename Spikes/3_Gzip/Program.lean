import Grass.Emit
import Spikes.«3_Gzip».Bindings

namespace Grass.Spikes.Gzip

def gzipVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    using_component gzipImplementationBinding
    using_source_closure gzipSourceClosureComplete
    using_expansion gzipExpansionExact
    with gzipExpandedSource

def bytes : ByteArray := emitProgram gzipVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  gzipVerified.sound

end Grass.Spikes.Gzip
