import Grass.Std.Zlib.Fixed32K
import Spikes.«3_Gzip».Spec

namespace Grass.Spikes.Gzip

def codecPlan : GzipImplementationPlan :=
  .fixed32KHashChain (maxProbes := 64)

def fixed32KContract : ComponentContract :=
  Std.Zlib.Fixed32K.contract codecPlan

def fixed32KModel : ImplementationModel :=
  Std.Zlib.Fixed32K.model codecPlan

theorem fixed32KModelCorrect :
    ImplementationRealizesContract fixed32KModel fixed32KContract :=
  Std.Zlib.Fixed32K.correct codecPlan

theorem fixed32KRoundTrip (input : ByteArray) :
    Std.Zlib.inflate (Std.Zlib.Fixed32K.write codecPlan input) = .ok input :=
  Std.Zlib.Fixed32K.roundTrip codecPlan input

def fixed32KFunctionContract : SerialFunctionContract :=
  SerialFunctionContract.ofComponent fixed32KContract
    (Std.Zlib.Fixed32K.terminates codecPlan)
    (Std.Zlib.Fixed32K.noExternalFrontier codecPlan)

end Grass.Spikes.Gzip
