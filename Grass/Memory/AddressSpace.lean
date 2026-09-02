import Grass.Core.Context
import Grass.Core.Name
import Grass.Core.Uid

/-!
# Address spaces and addresses

`docs/MEMORY_MODEL.md` §7.5 is explicit that CPU virtual memory, physical memory,
device memory, Wasm memories, GPU storage classes, and externally owned buffers
are not interchangeable merely because their offsets match. An address space
identity is therefore part of provenance, and a numerically equal address in a
different space is a different location.

## Not every address is a number

Spike 5 declares `OpMemoryModel Logical GLSL450` (`docs/SPIKE_5.md`), and in
SPIR-V's Logical addressing model a pointer has **no numeric address at all**: it
is an `%id` in a storage class, reached by `OpAccessChain`, and there is no width
to bound because there is no number to bound. A fixed `BitVec 64` address would
force a fabricated number for `%positionsVar`, which is semantic invention
(`docs/FOUNDATION.md` law 1) dressed as a representation detail.

`Address` therefore has two forms and the space says which one it uses.
`Representable` rejects the mismatch rather than coercing: a numeric address in a
symbolic space is not "close enough", it is rejected, per law 8.

## What `Representable` is not

`Representable` is a *necessary* condition — the address is well formed for its
space's representation. It is not the profile's validity predicate. x86-64
canonicality is sign-extension of bit 47, not an unsigned magnitude bound, so a
width test both rejects canonical high-half addresses and admits non-canonical
ones. That predicate belongs to the ISA profile, which owns its own address
validity; §10's required proof package is where it is discharged.
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

/-- A SPIR-V `Private` storage class under the Logical addressing model. -/
def spirvPrivate : AddressSpaceId := ⟨⟨"spirv.private"⟩⟩

/-- A SPIR-V `Input` storage class under the Logical addressing model. -/
def spirvInput : AddressSpaceId := ⟨⟨"spirv.input"⟩⟩

/-- A SPIR-V `Output` storage class under the Logical addressing model. -/
def spirvOutput : AddressSpaceId := ⟨⟨"spirv.output"⟩⟩

/-- A SPIR-V `PushConstant` storage class under the Logical addressing model. -/
def spirvPushConstant : AddressSpaceId := ⟨⟨"spirv.pushConstant"⟩⟩

end AddressSpaceId

/-- The identity of a memory type, which fixes caching behavior. -/
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

/-- Storage with no host-side caching semantics, such as a SPIR-V storage class. -/
def notHostCached : MemoryTypeId := ⟨⟨"notHostCached"⟩⟩

end MemoryTypeId

/--
Whether storage in a space is coherent with the host without explicit action.

`docs/MEMORY_MODEL.md` §7.5: "Noncoherent profiles require explicit
visibility/cache operations." This is a field a profile can read rather than a
string it must compare, because the obligation to issue a cache-maintenance or
visibility operation depends on it.
-/
inductive Coherence where
  /-- Writes become visible to the host without an explicit operation. -/
  | hostCoherent
  /-- Visibility requires an explicit cache-maintenance or barrier operation. -/
  | requiresExplicitVisibility
  /-- A coherence discipline owned by one profile. -/
  | profileSpecific (name : Name)
deriving DecidableEq, Repr

/-- How addresses in a space are represented. -/
inductive AddressRepr where
  /-- Flat numeric addresses of `bits` significant bits, at most 64. -/
  | numeric (bits : Nat)
  /-- Opaque symbolic identifiers with no numeric address, as in SPIR-V's
  Logical addressing model. -/
  | symbolic
deriving DecidableEq, Repr

/-- Phantom tag for symbolic address identities. -/
inductive SymbolicAddressTag : Type

/-- The identity of a symbolic address, such as a SPIR-V `%id`. -/
abbrev SymbolicAddressId := Uid SymbolicAddressTag

/-- A machine address in a numerically addressed space. -/
abbrev MachineAddress := BitVec 64

/--
An address.

The two forms are not interchangeable and there is no coercion between them.
Which one a space admits is fixed by its `repr`, and `AddressSpace.Representable`
rejects a mismatch.
-/
inductive Address where
  /-- A numeric address. -/
  | numeric (value : MachineAddress)
  /-- An opaque symbolic address with no numeric value. -/
  | symbolic (id : SymbolicAddressId)
deriving DecidableEq, Repr

namespace Address

/-- The numeric value of an address, when it has one. -/
def value? : Address → Option MachineAddress
  | .numeric value => some value
  | .symbolic _ => none

@[simp] theorem value?_numeric (value : MachineAddress) :
    (Address.numeric value).value? = some value := rfl

@[simp] theorem value?_symbolic (id : SymbolicAddressId) :
    (Address.symbolic id).value? = none := rfl

end Address

/--
An address space: its identity, how its addresses are represented, its memory
type, its coherence, and, for externally owned storage, the agent that owns it.
-/
structure AddressSpace where
  /-- Which space this is. -/
  id : AddressSpaceId
  /-- How addresses in this space are represented. -/
  repr : AddressRepr
  /-- The caching behavior of storage in this space. -/
  memoryType : MemoryTypeId
  /-- Whether host visibility needs an explicit operation. -/
  coherence : Coherence
  /-- The agent that owns this storage, for externally owned buffers. `none`
  means the program's own address space. `docs/MEMORY_MODEL.md` §7.5 treats
  externally owned buffers as a distinct space, so the owner is part of the
  space's identity rather than a property of individual allocations. -/
  owner : Option ContextId := none
deriving DecidableEq, Repr

namespace AddressSpace

/--
`space.WellFormed` holds when the space's declared representation is realizable.

A numeric space wider than the 64 bits `MachineAddress` provides is not a space
this vocabulary version can express; per `docs/MEMORY_MODEL.md` §9 that is a
versioned extension, and it must be rejected here rather than silently accepted
by a bound nothing checks.
-/
def WellFormed (space : AddressSpace) : Prop :=
  match space.repr with
  | .numeric bits => bits ≤ 64
  | .symbolic => True

instance (space : AddressSpace) : Decidable space.WellFormed := by
  unfold WellFormed
  split <;> infer_instance

/--
`space.Representable addr` holds when `addr` is a well-formed address for
`space`.

Necessary, not sufficient. See the module comment: a profile's own validity
predicate, such as x86-64 canonicality, is stronger and is owned by the profile.
-/
def Representable (space : AddressSpace) (addr : Address) : Prop :=
  match space.repr, addr with
  | .numeric bits, .numeric value => value.toNat < 2 ^ bits
  | .symbolic, .symbolic _ => True
  | _, _ => False

instance (space : AddressSpace) (addr : Address) : Decidable (space.Representable addr) := by
  unfold Representable
  split <;> infer_instance

/-- A numeric address is not representable in a symbolic space. There is no
coercion, and no fabricated number. -/
@[simp] theorem not_representable_numeric_in_symbolic
    {space : AddressSpace} (h : space.repr = .symbolic) (value : MachineAddress) :
    ¬ space.Representable (.numeric value) := by
  simp [Representable, h]

/-- A symbolic address is not representable in a numeric space. -/
@[simp] theorem not_representable_symbolic_in_numeric
    {space : AddressSpace} {bits : Nat} (h : space.repr = .numeric bits)
    (id : SymbolicAddressId) : ¬ space.Representable (.symbolic id) := by
  simp [Representable, h]

/-- The ordinary 64-bit write-back CPU space used by the initial profile. -/
def cpuVirtual64 : AddressSpace :=
  { id := .cpuVirtual, repr := .numeric 64, memoryType := .writeBack
    coherence := .hostCoherent }

/-- A SPIR-V `Private` storage class under the Logical addressing model. -/
def spirvPrivate : AddressSpace :=
  { id := .spirvPrivate, repr := .symbolic, memoryType := .notHostCached
    coherence := .requiresExplicitVisibility }

@[simp] theorem wellFormed_cpuVirtual64 : cpuVirtual64.WellFormed := by
  simp [WellFormed, cpuVirtual64]

@[simp] theorem wellFormed_spirvPrivate : spirvPrivate.WellFormed := trivial

/-- Every 64-bit value is representable in a space declaring the full width. -/
theorem representable_of_bits_eq_64 {space : AddressSpace} (h : space.repr = .numeric 64)
    (value : MachineAddress) : space.Representable (.numeric value) := by
  simpa [Representable, h] using value.isLt

/-- Every symbolic address is representable in a symbolic space; there is no
width to check. -/
theorem representable_symbolic {space : AddressSpace} (h : space.repr = .symbolic)
    (id : SymbolicAddressId) : space.Representable (.symbolic id) := by
  simp [Representable, h]

end AddressSpace

end Grass.Memory
