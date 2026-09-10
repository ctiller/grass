import Grass.Memory.InitializedRegion

/-! Compatibility names for the shared initialized-region installer. -/
namespace Grass.Platform.Win32

export Grass.Memory (InitializedRegion MemoryFresh installInitializedRegion?)
export Grass.Memory.MemoryFresh (grant_root_ne allocation_backing_ne)
export Grass.Memory.InitializedRegion (cellAt?_of_lookups)
export Grass.Memory (installInitializedRegion?_admitted
  installInitializedRegion?_eq_none_of_grant_root
  installInitializedRegion?_eq_none_of_allocation_backing
  installInitializedRegion?_allocation installInitializedRegion?_fresh
  installInitializedRegion?_allocation_absent installInitializedRegion?_allocation_ne
  installInitializedRegion?_backing installInitializedRegion?_backing_ne
  installInitializedRegion?_cellAt?)

end Grass.Platform.Win32
