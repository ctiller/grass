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

/--
What representation an identity this module names requires.

Two answers, and there were three: `anyRepresentation` was the default for every
identity this module does not name, on the reasoning that most identities are a
profile's own and this module has nothing to say about them.

**That default was the round-fifteen attack, still live under a fresh name.** Review
declared a CPU space under the identity `win32.processHeap` with `repr := .symbolic`,
and it was well formed, its table was well formed, and a store of `2 ^ 70` bytes at a
symbolic address demanding 4096-byte alignment passed both the descriptor seal and
`Substep.WellFormedIn` -- because `AccessDescriptor.WellFormedIn`'s `aligned` and
`rangeFitsSpace` are both vacuous for a symbolic representation. §4.4.1a's table said
"nothing about a space is a profile's choice now except which identity it declares",
and that was true of the eight identities named below and of no others.

So the default is numeric. A genuinely symbolic new space is added to
`requiredRepresentation` here, in the open, which is what `docs/FOUNDATION.md` law 8
asks of an unknown: reject it rather than approximate it as the permissive case. The
cost is that a vendor with a symbolic address model edits this module, and that is the
right cost -- every numeric guard in the seal is off for such a space, so admitting one
sight unseen is admitting a descriptor nothing bounds.
-/
inductive RepresentationDemand where
  /-- Addresses in this space are machine addresses. -/
  | numericallyAddressed
  /-- The space has no machine addresses at all. -/
  | symbolicallyAddressed
deriving DecidableEq, Repr

/--
The representation each named identity requires.

Kind only, never width: how many bits a CPU virtual space has is a profile's answer
and `AddressSpace.WellFormed`'s 64-bit bound is the only limit on it. What is not a
profile's answer is whether `cpu.virtual` has machine addresses, because
`AccessDescriptor.WellFormedIn`'s alignment and range-width clauses are both vacuous
without them -- see `AddressSpace.RepresentationMatchesIdentity`.

The SPIR-V identities are symbolic because the Logical addressing model has no
addresses to represent; `docs/MEMORY_MODEL.md` §7.5 lists GPU storage classes among
the spaces that are not interchangeable with the rest.
-/
def requiredRepresentation (id : AddressSpaceId) : RepresentationDemand :=
  if id = spirvPrivate || id = spirvInput || id = spirvOutput ||
      id = spirvPushConstant then
    .symbolicallyAddressed
  else
    .numericallyAddressed

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
  means the program's own address space, and `docs/MEMORY_MODEL.md` §7.5 treats
  externally owned buffers as a distinct space.

  **Carried and unread.** Nothing projects it. An earlier version of this docstring
  said the owner is "part of the space's identity rather than a property of
  individual allocations", and that is false in any operational sense:
  `AddressSpaceTable.find?` matches on `space.id`, `WellFormed` requires
  `(spaces.map AddressSpace.id).Nodup`, and two externally owned buffers with
  different owners and one id cannot be told apart. Review found it, and found why no
  gate did: `Tools/ConsultedAudit.py` keys on the field *name*, and `owner` is
  projected freely elsewhere as `Obligation.owner`, which is the same-name blind spot
  that tool's own docstring documents.

  It is kept rather than deleted because §7.5's distinction is real and a device
  authority will need it; `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 lists it with the
  other facts the model carries and nothing consults. -/
  owner : Option ContextId := none
deriving DecidableEq, Repr

namespace AddressSpace

/--
`space.RepresentationMatchesIdentity` holds when the space's representation is the one
its identity requires.

**This exists because `repr` was a profile input that could only remove refusals**,
which `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1a says a profile input must never be.
`AccessDescriptor.WellFormedIn` reads it twice -- `aligned` and `rangeFitsSpace` are
both vacuous for a symbolic representation, because there is no numeric address to
align and no width to exceed. A table declaring `cpu.virtual` with `repr := .symbolic`
*once* was well formed, so `StepPolicy.vocabularyWellFormed` was dischargeable, and
against that space a store of more than `2^64` bytes at a symbolic address with a
4096-byte alignment demand passed both the descriptor seal and `Substep.WellFormedIn`.
Review built it and stepped it.

`AccessDescriptor.WellFormedIn`'s docstring named that exact attack and said the seal
was resolution through the profile's table plus the ambiguity check. Those close the
hand-made space and the duplicate; neither closes a table that declares the pairing
once. The tree's own fixture wrote the value down and refused it as a duplicate.

Every identity is constrained, and only in kind. It used to be only the eight this
module names, on the reasoning that a profile with a genuinely new space uses a new
identity and this should say nothing about it -- and review then declared a hostile
space under a new identity and walked the same attack through. `AllocationSourceId` is
not the right analogy: a source is a fact about storage that no rule reads twice,
whereas a representation switches two clauses of the declaration-time seal off.
-/
def RepresentationMatchesIdentity (space : AddressSpace) : Prop :=
  match space.id.requiredRepresentation with
  | .numericallyAddressed => space.repr ≠ .symbolic
  | .symbolicallyAddressed => space.repr = .symbolic

instance (space : AddressSpace) : Decidable space.RepresentationMatchesIdentity := by
  unfold RepresentationMatchesIdentity
  split <;> infer_instance

/--
`space.WellFormed` holds when the space's declared representation is realizable and is
the one its identity requires.

A numeric space of any width but 64 is not a space this vocabulary version can
express; per `docs/MEMORY_MODEL.md` §9 that is a versioned extension, and it must be
rejected here rather than silently accepted by a bound nothing checks.

**The bound was `bits ≤ 64` and a narrower space was admissible**, which review found
was admissible in the wrong way. `MachineAddress` is 64 bits and
`Grass/Memory/Addressing.lean`'s `FitsAllocation` compares against `2 ^ 64`, so for a
32-bit space the wrap check ran in the wrong modulus: an allocation based at
`2 ^ 32 - 16` with a 64-byte extent satisfied `FitsAllocation`, `placementWraps` did not
fire, and `distinct_allocations_do_not_alias` then yielded distinct machine addresses
for two offsets that are *the same byte* in the space the profile declared. The bridge a
profile is meant to cite was being discharged in 64-bit arithmetic for a space that is
not 64 bits.

Not reachable through `step` today, because an access at that offset must declare an
address `addressRepresentable` rejects in a 32-bit space -- so it was latent, and
latent in exactly the way `Addressing.lean` exists to worry about. The alternative
repair is to make `FitsAllocation` and the placement checks take the space, which
`denialOf` cannot do without the resolved `AddressSpace` in hand;
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records that as what a future vocabulary
version does instead of this.
-/
def WellFormed (space : AddressSpace) : Prop :=
  (match space.repr with
   | .numeric bits => bits = 64
   | .symbolic => True) ∧ space.RepresentationMatchesIdentity

instance (space : AddressSpace) : Decidable space.WellFormed := by
  unfold WellFormed
  refine instDecidableAnd (dp := ?_) (dq := inferInstance)
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

@[simp] theorem wellFormed_cpuVirtual64 : cpuVirtual64.WellFormed := by decide

@[simp] theorem wellFormed_spirvPrivate : spirvPrivate.WellFormed := by decide

/-- **`cpu.virtual` cannot be declared symbolically addressed.** The attack
`AccessDescriptor.WellFormedIn`'s docstring names, refused at the table where the
docstring said the seal was. -/
theorem not_wellFormed_symbolic_cpuVirtual :
    ¬ ({ cpuVirtual64 with repr := .symbolic } : AddressSpace).WellFormed := by decide

/-- And a SPIR-V storage class cannot be declared numerically addressed, which is the
same rule read the other way: `Representable` would then admit a machine address for a
space that has none. -/
theorem not_wellFormed_numeric_spirvPrivate :
    ¬ ({ spirvPrivate with repr := .numeric 64 } : AddressSpace).WellFormed := by decide

/-- **An identity this module does not name is numerically addressed**, which is the
default a profile cannot argue with. It used to be unconstrained, and review declared a
symbolic space under `win32.processHeap` -- an allocator name Spike 1's own profile uses
-- and put a store of `2 ^ 70` bytes at a symbolic address through the seal with a
4096-byte alignment demand, both numeric clauses vacuous. -/
theorem an_unnamed_identity_is_numerically_addressed :
    ¬ ({ cpuVirtual64 with id := ⟨⟨"win32.processHeap"⟩⟩, repr := .symbolic } :
      AddressSpace).WellFormed ∧
    ({ cpuVirtual64 with id := ⟨⟨"win32.processHeap"⟩⟩ } : AddressSpace).WellFormed := by
  exact ⟨by decide, by decide⟩

/-- **A narrow numeric space is not well formed**, and this theorem asserted the
opposite for a day. `MachineAddress` and `FitsAllocation` are fixed at 64 bits, so a
32-bit space had its wrap check run in the wrong modulus; see `WellFormed` above. -/
theorem a_narrow_numeric_cpu_space_is_not_well_formed :
    ¬ ({ cpuVirtual64 with repr := .numeric 32 } : AddressSpace).WellFormed := by decide

/-- **Every identity this module names is constrained**, not only the two the theorems
above happen to exercise. Review mutated `requiredRepresentation` down to `cpuVirtual`
and `spirvPrivate` alone and the whole tree stayed green, so six of the eight -- the
two device spaces §7.5 needs among them -- could have regressed invisibly. -/
theorem every_named_identity_constrains_its_representation :
    [AddressSpaceId.cpuVirtual, .cpuPhysical, .deviceLocal, .deviceHostVisible].all
      (fun id => !decide (({ cpuVirtual64 with id := id, repr := .symbolic } :
        AddressSpace).WellFormed)) = true ∧
    [AddressSpaceId.spirvPrivate, .spirvInput, .spirvOutput, .spirvPushConstant].all
      (fun id => !decide (({ spirvPrivate with id := id, repr := .numeric 64 } :
        AddressSpace).WellFormed)) = true ∧
    [AddressSpaceId.cpuVirtual, .cpuPhysical, .deviceLocal, .deviceHostVisible].all
      (fun id => decide (({ cpuVirtual64 with id := id } : AddressSpace).WellFormed))
        = true ∧
    [AddressSpaceId.spirvPrivate, .spirvInput, .spirvOutput, .spirvPushConstant].all
      (fun id => decide (({ spirvPrivate with id := id } : AddressSpace).WellFormed))
        = true := by
  exact ⟨by decide, by decide, by decide, by decide⟩

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

/--
The address spaces a profile declares, resolvable by identity.

This exists because an access must not be able to describe its own address space.
If a descriptor carried an `AddressSpace` value, an author could pair the id
`cpu.virtual` with `repr := .symbolic` and switch off both the address-width and
the range-bound checks, since each is conditioned on the representation the
descriptor itself asserted. Every guard would then be optional in practice.

A descriptor therefore names a space by `AddressSpaceId`, and the properties of
that space come from here — from the profile, which owns what its target's
address spaces are. `docs/MEMORY_MODEL.md` §7.5 makes spaces non-interchangeable;
that is only enforceable if something other than the access decides what a space
is.
-/
structure AddressSpaceTable where
  /-- The declared spaces. -/
  spaces : List AddressSpace
deriving Repr

namespace AddressSpaceTable

/-- The table declaring nothing. It resolves no space, so it admits no access. -/
def empty : AddressSpaceTable := ⟨[]⟩

/-- Resolve a space by identity. `none` for a space this profile never declared,
which is the rejection `docs/FOUNDATION.md` law 8 requires. -/
def find? (table : AddressSpaceTable) (id : AddressSpaceId) : Option AddressSpace :=
  table.spaces.find? fun space => space.id = id

/-- `table.Declares id` holds when the table resolves `id`. -/
def Declares (table : AddressSpaceTable) (id : AddressSpaceId) : Prop :=
  (table.find? id).isSome

instance (table : AddressSpaceTable) (id : AddressSpaceId) : Decidable (table.Declares id) :=
  inferInstanceAs (Decidable (_ = _))

@[simp] theorem find?_empty (id : AddressSpaceId) : empty.find? id = Option.none := rfl

@[simp] theorem not_declares_empty (id : AddressSpaceId) : ¬ empty.Declares id := by
  simp [Declares]

/-- A resolved space really is the one that was asked for, so a table cannot
answer with a space under the wrong name. -/
theorem id_of_find? {table : AddressSpaceTable} {id : AddressSpaceId} {space : AddressSpace}
    (h : table.find? id = some space) : space.id = id := by
  have := List.find?_some h
  simpa using this

/--
`table.WellFormed` holds when every declared space is realizable and no identity
is declared twice.

Without it the law-8 chain terminated in an unchecked record: a table could list
`cpu.virtual` twice, once honestly and once with `repr := .symbolic`, and
`find?` returns the first match. Resolving a descriptor's space through the
profile is only a guarantee if the profile's own table is checked.
-/
def WellFormed (table : AddressSpaceTable) : Prop :=
  (∀ space ∈ table.spaces, space.WellFormed) ∧
  (table.spaces.map AddressSpace.id).Nodup

@[simp] theorem wellFormed_empty : empty.WellFormed := by
  simp [WellFormed, empty]

/-- The ordinary Win64 table: one 64-bit write-back CPU space. -/
def cpuOnly : AddressSpaceTable := ⟨[AddressSpace.cpuVirtual64]⟩

@[simp] theorem wellFormed_cpuOnly : cpuOnly.WellFormed := by
  refine ⟨?_, ?_⟩
  · intro space hs
    simp only [cpuOnly, List.mem_singleton] at hs
    exact hs ▸ AddressSpace.wellFormed_cpuVirtual64
  · simp [cpuOnly]

@[simp] theorem find?_cpuOnly : cpuOnly.find? .cpuVirtual = some AddressSpace.cpuVirtual64 :=
  rfl

end AddressSpaceTable

end Grass.Memory
