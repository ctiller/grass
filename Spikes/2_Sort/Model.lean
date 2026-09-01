import Grass.Std.Sort.Stable
import Spikes.«2_Sort».Spec

namespace Grass.Spikes.Sort

def stableSortContract : ComponentContract :=
  StableSort.contract format order

def stableSortModel : ImplementationModel :=
  StableSort.bottomUpMergeModel format order

theorem stableSortModelCorrect :
    ImplementationRealizesContract stableSortModel stableSortContract :=
  StableSort.bottomUpMergeCorrect format order

def stableSortFunctionContract : SerialFunctionContract :=
  SerialFunctionContract.ofComponent stableSortContract
    StableSort.bottomUpTerminates
    StableSort.noExternalFrontier

end Grass.Spikes.Sort
