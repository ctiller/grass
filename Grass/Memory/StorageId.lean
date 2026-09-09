import Grass.Core.Uid

/-! Backing-storage identity, distinct from allocation/view provenance.
The owning execution must thread one fresh supply through storage creation and
must not reuse retired identities. The nominal type alone does not enforce that
history discipline. -/
namespace Grass.Memory

/-- Phantom tag for backing stores. -/
inductive StorageTag : Type

/-- Identity of shared byte storage, independent of addresses and view identity. -/
abbrev StorageId := Core.Uid StorageTag

end Grass.Memory
