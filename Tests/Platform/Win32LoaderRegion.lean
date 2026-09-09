import Grass.Platform.Win32.LoaderRegion

/-! Focused executable checks for the one-region bookkeeping helper. -/

namespace Tests.Platform.Win32LoaderRegion

open Grass.Core Grass.Memory Grass.Platform.Win32 Grass.Std.Logical

private def allocations : FreshSupply AllocTag := .initial
private def storages : FreshSupply StorageTag := .initial
private def epochs : FreshSupply EpochTag := .initial
private def contexts : FreshSupply ContextTag := .initial

private def region : InitializedRegion :=
  { allocId := allocations.fresh.1
    storageId := storages.fresh.1
    epoch := epochs.fresh.1
    base := 0x400000
    permission := .readWrite
    source := .imageMapping
    owner := contexts.fresh.1
    bytes := Vec.fromList [0x4d, 0x5a] }

private def installed : MemoryState :=
  (installInitializedRegion? MemoryState.empty region).getD MemoryState.empty

/-- Reusing the same represented allocation identity is refused. -/
example : installInitializedRegion? installed region = none := by decide

/-- Successful installation exposes the initialized stored byte. -/
example : installed.cellAt? region.allocId 0 = some (0x4d, true) := by decide

end Tests.Platform.Win32LoaderRegion
