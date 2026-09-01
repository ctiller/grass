import Grass.Platform.Win10.X64
import Spikes.«3_Gzip».Spec

namespace Grass.Spikes.Gzip

def policy : TargetOutcomeProjection GzipOutcome UInt32 :=
  .successOrFailure
    (success := GzipOutcome.success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ByteStreams policy

end Grass.Spikes.Gzip
