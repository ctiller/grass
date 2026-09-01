import Grass.Platform.Win10.X64
import Spikes.«2_Sort».Spec

namespace Grass.Spikes.Sort

def policy : TargetOutcomeProjection SortOutcome UInt32 :=
  .successOrFailure
    (success := .success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ByteStreams policy

end Grass.Spikes.Sort
