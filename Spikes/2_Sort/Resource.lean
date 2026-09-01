import Grass.Spec.Resource

namespace Grass.Spikes.Sort

def resources : ConsoleBufferResourceModel :=
  ConsoleBufferResourceModel.untilMemoryExhaustion
    (onExhaustion := .terminateWithNoOutput)
    (capacity := .noArtificialLimit)

end Grass.Spikes.Sort
