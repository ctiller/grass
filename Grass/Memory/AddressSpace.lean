import Grass.Core.Name

/-!
# Address spaces and machine addresses

`docs/MEMORY_MODEL.md` §7.5 is explicit that CPU virtual memory, physical
memory, device memory, Wasm memories, GPU storage classes, and externally owned
buffers are not interchangeable merely because their offsets match. An address
space identity is therefore part of provenance, and a numerically equal address
in a different space is a different location.

Address-space and memory-type identities are open nominal names rather than a
closed enumeration, so a platform or device profile introduces its own without
editing this module. The names defined here are the ones the corpus already
mentions; they are definitions, not constructors, and carry no privilege.
-/

namespace Grass.Memory

open Grass.Core

/-- The identity of an address space. -/
structure AddressSpaceId where
  /-- The space's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace AddressSpaceId

/-- Ordinary CPU virtual memory. -/
def cpuVirtual : AddressSpaceId := ⟨⟨"cpu.virtual"⟩⟩

/-- Physical memory as seen through a page-table or firmware view. -/
def cpuPhysical : AddressSpaceId := ⟨⟨"cpu.physical"⟩⟩

/-- Memory local to a device and not addressable by the host. -/
def deviceLocal : AddressSpaceId := ⟨⟨"device.local"⟩⟩

/-- Device memory mapped into the host's address space. -/
def deviceHostVisible : AddressSpaceId := ⟨⟨"device.hostVisible"⟩⟩

end AddressSpaceId

/-- The identity of a memory type, which fixes caching and coherence behavior. -/
structure MemoryTypeId where
  /-- The memory type's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace MemoryTypeId

/-- Ordinary cacheable write-back memory. This is the only type the initial
single-threaded profile admits, per `docs/MEMORY_MODEL.md` §9. -/
def writeBack : MemoryTypeId := ⟨⟨"writeBack"⟩⟩

/-- Write-combining memory, whose store visibility rules differ from write-back. -/
def writeCombining : MemoryTypeId := ⟨⟨"writeCombining"⟩⟩

/-- Uncacheable memory. -/
def uncached : MemoryTypeId := ⟨⟨"uncached"⟩⟩

end MemoryTypeId

/--
A machine address, as a 64-bit value.

The width is fixed here rather than made a parameter of every address-bearing
type, because a dependent width would propagate through the access descriptor,
the event vocabulary, and every instruction model for no present benefit. Spaces
narrower than 64 bits are represented by an `AddressSpace.addressBits` bound and
the `AddressSpace.FitsWidth` predicate, which is enough for Wasm memories, GPU
storage classes, and 32-bit device apertures.

A target *wider* than 64 bits is the case this does not cover. Per
`docs/MEMORY_MODEL.md` §9 that is a versioned extension of a foundational
vocabulary, requiring a migration theorem and renewed review, not a silent
widening.
-/
abbrev MachineAddress := BitVec 64

/--
An address space: its identity, its usable address width, and its memory type.
-/
structure AddressSpace where
  /-- Which space this is. -/
  id : AddressSpaceId
  /-- The number of significant address bits, at most 64. -/
  addressBits : Nat
  /-- The caching and coherence behavior of storage in this space. -/
  memoryType : MemoryTypeId
deriving DecidableEq, Repr

namespace AddressSpace

/-- `space.FitsWidth addr` holds when `addr` is representable in `space`. -/
def FitsWidth (space : AddressSpace) (addr : MachineAddress) : Prop :=
  addr.toNat < 2 ^ space.addressBits

instance (space : AddressSpace) (addr : MachineAddress) : Decidable (space.FitsWidth addr) :=
  inferInstanceAs (Decidable (_ < _))

/-- The ordinary 64-bit write-back CPU space used by the initial profile. -/
def cpuVirtual64 : AddressSpace :=
  { id := .cpuVirtual, addressBits := 64, memoryType := .writeBack }

/-- Every 64-bit value fits a space declaring the full width. -/
theorem fitsWidth_of_addressBits_eq_64 {space : AddressSpace}
    (h : space.addressBits = 64) (addr : MachineAddress) : space.FitsWidth addr := by
  simpa [FitsWidth, h] using addr.isLt

end AddressSpace

end Grass.Memory
