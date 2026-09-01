import Grass.Spec.Resource

namespace Grass.Spikes.Gzip

def resources : StreamingResourceModel :=
  StreamingResourceModel.console
    |>.withResidentMemory .boundedIndependentOfInputLength

end Grass.Spikes.Gzip
