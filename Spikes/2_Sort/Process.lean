import Grass.Process.Sequential
import Spikes.«2_Sort».Spec

namespace Grass.Spikes.Sort

def processRealization : ProcessRealization spec :=
  ProcessRealization.standard (Grass.Std.Realizers.lookupExact spec)

end Grass.Spikes.Sort
