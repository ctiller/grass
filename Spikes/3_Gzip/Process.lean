import Grass.Process.Sequential
import Spikes.«3_Gzip».Spec

namespace Grass.Spikes.Gzip

def processRealization : ProcessRealization spec :=
  ProcessRealization.standard (Grass.Std.Realizers.lookupExact spec)

end Grass.Spikes.Gzip
