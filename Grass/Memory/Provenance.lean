import Grass.Core.Uid
import Grass.Core.Name
import Grass.Memory.AddressSpace
import Grass.Memory.Range

/-!
# Provenance

`docs/MEMORY_MODEL.md` §2 fixes the central rule: every allocation has a fresh
generative identity independent of its numerical address, and address reuse never
revives old pointers. Provenance, not the address, is what authorizes an access.

The structural consequence is visible in `Provenance` below. Two provenances that
differ in `root` or `epoch` are unequal whatever their addresses are, so a
recycled address cannot produce an equal provenance by arithmetic accident. The
operational half of that guarantee — that an allocator actually mints a fresh
root and advances an epoch on reuse — belongs to the allocator and arena
milestone (M6 of `docs/MEMORY_IMPLEMENTATION_PLAN.md`) and is not claimed here.

The hierarchy §2 describes is carried as a path of nominal steps rather than a
closed inductive of shapes. `provider allocation -> arena/block -> object ->
field`, `stack reservation -> call frame -> local slot`, and `image mapping ->
section -> symbol` are then three uses of one mechanism, and a profile that needs
a fourth adds a step kind instead of editing this module.
-/

namespace Grass.Memory

open Grass.Core

/-- Phantom tag for allocation identities. -/
inductive AllocTag : Type

/-- Phantom tag for epoch identities. -/
inductive EpochTag : Type

/--
The generative identity of an allocation.

Independent of address by construction: nothing in this type mentions one.
-/
abbrev AllocId := Core.Uid AllocTag

/--
The reuse generation of an allocation's storage.

`docs/MEMORY_MODEL.md` §5 requires an arena to advance an epoch before reusing
storage, so that same-address objects in a new epoch have new provenance.
-/
abbrev EpochId := Core.Uid EpochTag

/-- The identity of an allocation source, such as a specific OS or library allocator. -/
structure AllocationSourceId where
  /-- The source's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace AllocationSourceId

/-- Win32 `VirtualAlloc` reservations. -/
def virtualAlloc : AllocationSourceId := ⟨⟨"win32.virtualAlloc"⟩⟩

/-- The process heap. -/
def processHeap : AllocationSourceId := ⟨⟨"processHeap"⟩⟩

/-- A C `malloc` family allocator. -/
def malloc : AllocationSourceId := ⟨⟨"malloc"⟩⟩

/-- A bump or arena allocator carving from an upstream block. -/
def bumpAllocator : AllocationSourceId := ⟨⟨"bumpAllocator"⟩⟩

/-- Stack storage belonging to a live call frame. -/
def stack : AllocationSourceId := ⟨⟨"stack"⟩⟩

/-- A loaded image mapping. -/
def imageMapping : AllocationSourceId := ⟨⟨"imageMapping"⟩⟩

/-- A memory-mapped file. -/
def mappedFile : AllocationSourceId := ⟨⟨"mappedFile"⟩⟩

/-- Storage owned by a device rather than the host allocator. -/
def deviceMemory : AllocationSourceId := ⟨⟨"deviceMemory"⟩⟩

end AllocationSourceId

/-- The identity of a kind of provenance step, such as a field or a stack slot. -/
structure ProvenanceStepKind where
  /-- The step kind's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace ProvenanceStepKind

/-- An arena or allocator block carved from a provider allocation. -/
def block : ProvenanceStepKind := ⟨⟨"block"⟩⟩

/-- A whole object within its allocation or block. -/
def object : ProvenanceStepKind := ⟨⟨"object"⟩⟩

/-- A field or subobject within an object. -/
def field : ProvenanceStepKind := ⟨⟨"field"⟩⟩

/-- One call frame within a stack reservation. -/
def frame : ProvenanceStepKind := ⟨⟨"frame"⟩⟩

/-- A local slot within a call frame. -/
def slot : ProvenanceStepKind := ⟨⟨"slot"⟩⟩

/-- An image section within a mapping. -/
def imageSection : ProvenanceStepKind := ⟨⟨"imageSection"⟩⟩

/-- A symbol or object within an image section. -/
def symbol : ProvenanceStepKind := ⟨⟨"symbol"⟩⟩

end ProvenanceStepKind

/--
One step of a provenance path.

`extent` is relative to the *root allocation*, not to the parent step. Absolute
extents make nesting a plain `ByteRange.Contains` check and keep a deep path from
accumulating an addition chain in every bounds proof.
-/
structure ProvenanceStep where
  /-- What kind of step this is. -/
  kind : ProvenanceStepKind
  /-- The step's name within its parent, such as a field or section name. -/
  label : Name
  /-- The step's byte extent, relative to the root allocation. -/
  extent : ByteRange
deriving DecidableEq, Repr

/--
The provenance of a location or pointer.

Equality is structural, so a provenance with a different `root`, `epoch`, or
`space` is a different provenance regardless of any address.
-/
structure Provenance where
  /-- The address space this provenance lives in. -/
  space : AddressSpaceId
  /-- The generative identity of the root allocation. -/
  root : AllocId
  /-- The reuse generation of that allocation's storage. -/
  epoch : EpochId
  /-- Which allocator or mapping produced the root allocation. -/
  source : AllocationSourceId
  /-- The hierarchical path from the root allocation to what this designates. -/
  path : List ProvenanceStep
deriving DecidableEq, Repr

namespace Provenance

/--
The byte extent this provenance designates, relative to its root allocation.

`none` means the whole root allocation: an empty path designates the allocation
itself, whose size is held by the allocation table rather than by the provenance.
-/
def extent? (p : Provenance) : Option ByteRange := p.path.getLast?.map (·.extent)

/-- `NestedPath steps` holds when each step lies within the step before it. -/
def NestedPath : List ProvenanceStep → Prop
  | [] => True
  | [_] => True
  | parent :: child :: rest =>
      parent.extent.Contains child.extent ∧ NestedPath (child :: rest)

/--
`p.Nested` holds when each step of the path lies within its parent.

An unnested path is not a provenance of anything, so this is a well-formedness
condition consumers must establish, not a fact about arbitrary `Provenance`
values. Descending therefore requires a containment proof; it is not free.
-/
def Nested (p : Provenance) : Prop := NestedPath p.path

@[simp] theorem nestedPath_nil : NestedPath [] := trivial

@[simp] theorem nestedPath_singleton (step : ProvenanceStep) : NestedPath [step] := trivial

theorem NestedPath.tail {parent child : ProvenanceStep} {rest : List ProvenanceStep}
    (h : NestedPath (parent :: child :: rest)) : NestedPath (child :: rest) := h.2

theorem NestedPath.head {parent child : ProvenanceStep} {rest : List ProvenanceStep}
    (h : NestedPath (parent :: child :: rest)) :
    parent.extent.Contains child.extent := h.1

/-- Two provenances designate the same storage generation. -/
def SameStorage (p q : Provenance) : Prop :=
  p.space = q.space ∧ p.root = q.root ∧ p.epoch = q.epoch

instance (p q : Provenance) : Decidable (p.SameStorage q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Provenances rooted in different allocations never designate the same storage. -/
theorem not_sameStorage_of_root_ne {p q : Provenance} (h : p.root ≠ q.root) :
    ¬ p.SameStorage q := fun hs => h hs.2.1

/--
Provenances in different epochs never designate the same storage.

This is the structural half of "same-address objects in a new epoch have new
provenance" (`docs/MEMORY_MODEL.md` §5). It holds by construction because no
address participates in the comparison.
-/
theorem not_sameStorage_of_epoch_ne {p q : Provenance} (h : p.epoch ≠ q.epoch) :
    ¬ p.SameStorage q := fun hs => h hs.2.2

/-- Provenances in different address spaces never designate the same storage,
however their offsets compare (`docs/MEMORY_MODEL.md` §7.5). -/
theorem not_sameStorage_of_space_ne {p q : Provenance} (h : p.space ≠ q.space) :
    ¬ p.SameStorage q := fun hs => h hs.1

theorem SameStorage.refl (p : Provenance) : p.SameStorage p := ⟨rfl, rfl, rfl⟩

theorem SameStorage.symm {p q : Provenance} (h : p.SameStorage q) : q.SameStorage p :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem SameStorage.trans {p q r : Provenance} (h₁ : p.SameStorage q)
    (h₂ : q.SameStorage r) : p.SameStorage r :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

/--
`p.Designates root` is the provenance obtained by appending one step.

Extending a path never changes the root, epoch, space, or source, so authority
derived for a parent is never silently widened by descending into it.
-/
def descend (p : Provenance) (step : ProvenanceStep) : Provenance :=
  { p with path := p.path ++ [step] }

@[simp] theorem descend_root (p : Provenance) (step : ProvenanceStep) :
    (p.descend step).root = p.root := rfl

@[simp] theorem descend_epoch (p : Provenance) (step : ProvenanceStep) :
    (p.descend step).epoch = p.epoch := rfl

@[simp] theorem descend_space (p : Provenance) (step : ProvenanceStep) :
    (p.descend step).space = p.space := rfl

theorem sameStorage_descend (p : Provenance) (step : ProvenanceStep) :
    p.SameStorage (p.descend step) := ⟨rfl, rfl, rfl⟩

@[simp] theorem extent?_descend (p : Provenance) (step : ProvenanceStep) :
    (p.descend step).extent? = some step.extent := by
  simp [extent?, descend]

end Provenance

/--
A pointer: a machine address together with its ghost provenance.

`docs/MEMORY_MODEL.md` §2 requires exactly this pairing, and requires that
ordinary integer loads do not manufacture provenance. Nothing in this type lets
an address alone produce a `PointerValue`; constructing one demands a provenance
the surrounding proof already holds. Recovering a pointer from an integer needs
the additional proof §2 describes and is not an operation of this module.

The provenance component is ghost and is removed by erasure. Erasure preservation
is `docs/INSTRUCTIONS.md` §2 and is proved where erasure is defined, not here.
-/
structure PointerValue where
  /-- The address. Numeric in a numerically addressed space, symbolic in one
  like SPIR-V's Logical model where a pointer has no numeric value at all. -/
  address : Address
  /-- The ghost provenance authorizing use of that address. -/
  provenance : Provenance
deriving DecidableEq, Repr

namespace PointerValue

/-- Two pointers with equal addresses but different storage are different
pointers. This is the statement that address equality is not pointer equality. -/
theorem ne_of_not_sameStorage {p q : PointerValue}
    (h : ¬ p.provenance.SameStorage q.provenance) : p ≠ q := by
  rintro rfl
  exact h (Provenance.SameStorage.refl _)

end PointerValue

end Grass.Memory
