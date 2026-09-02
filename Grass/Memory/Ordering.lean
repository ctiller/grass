import Grass.Core.Name

/-!
# Atomicity, ordering, and scope

`docs/MEMORY_MODEL.md` §7.1 fixes the portable ordering vocabulary and the rule
that governs it: an ordering request may be used "only where it has a proved
target meaning". Mapping a portable order onto an ISA or API operation requires a
refinement theorem, and an unsupported mapping is rejected.

The portable modes are therefore a closed list — the corpus enumerates exactly
five — with one open escape for a mode a profile genuinely owns. That escape is
deliberately not a general extension point: `IsPortable` distinguishes the two,
and a profile-specific mode carries no portable meaning at all, so nothing can
consume it without knowing which profile it came from.

This module is vocabulary only. It defines no strength order between modes,
because the strength relation that matters is the one a `ConsistencyProfile`
induces over a whole event graph (M8 of `docs/MEMORY_IMPLEMENTATION_PLAN.md`),
and a portable order defined here would be a second, unproved one.
-/

namespace Grass.Memory

open Grass.Core

/--
Whether an access is atomic with respect to its declared scope.

`docs/MEMORY_MODEL.md` §3 is explicit that atomics do not grant ordinary
non-atomic access, so this is not a modifier on an access but part of what
distinguishes one kind of access from another.
-/
inductive Atomicity where
  /-- An ordinary access, subject to the data-race prohibition. -/
  | nonAtomic
  /-- An atomic access, subject to its profile's ordering model. -/
  | atomic
deriving DecidableEq, Repr

/--
A requested memory ordering.

The five portable modes are those named in `docs/MEMORY_MODEL.md` §7.1.
`profileSpecific` carries a profile's own mode and has no portable meaning.
-/
inductive MemoryOrder where
  /-- No ordering beyond coherence. -/
  | relaxed
  /-- Later accesses in this context are not reordered before this one. -/
  | acquire
  /-- Earlier accesses in this context are not reordered after this one. -/
  | release
  /-- Both acquire and release. -/
  | acquireRelease
  /-- Participates in a single total order over all such operations. -/
  | sequentiallyConsistent
  /-- A mode owned by one profile, with no portable meaning. -/
  | profileSpecific (name : Name)
deriving DecidableEq, Repr

namespace MemoryOrder

/--
`order.IsPortable` holds when `order` is one of the five modes with a portable
meaning.

A consumer that accepts a non-portable order without knowing its profile is
exactly the "permissive fallback" `docs/FOUNDATION.md` law 8 forbids.
-/
def IsPortable : MemoryOrder → Prop
  | .profileSpecific _ => False
  | _ => True

instance : (order : MemoryOrder) → Decidable order.IsPortable
  | .relaxed | .acquire | .release | .acquireRelease | .sequentiallyConsistent =>
      .isTrue trivial
  | .profileSpecific _ => .isFalse (fun h => h)

@[simp] theorem isPortable_relaxed : IsPortable .relaxed := trivial

@[simp] theorem not_isPortable_profileSpecific (name : Name) :
    ¬ IsPortable (.profileSpecific name) := fun h => h

end MemoryOrder

/--
The scope over which an ordering or atomicity claim holds.

`docs/MEMORY_MODEL.md` §7.1 lists thread, process, device, and system, and allows
profile-specific scopes. A device fence that is system-scoped and one that is
device-scoped are different operations, so scope is not optional metadata.
-/
inductive MemoryScope where
  /-- Ordering is claimed only within one execution context. -/
  | thread
  /-- Ordering is claimed across the contexts of one process. -/
  | process
  /-- Ordering is claimed across the queues and invocations of one device. -/
  | device
  /-- Ordering is claimed across every agent in the system. -/
  | system
  /-- A scope owned by one profile. -/
  | profileSpecific (name : Name)
deriving DecidableEq, Repr

namespace MemoryScope

/-- `scope.IsPortable` holds when `scope` is one of the four portable scopes. -/
def IsPortable : MemoryScope → Prop
  | .profileSpecific _ => False
  | _ => True

instance : (scope : MemoryScope) → Decidable scope.IsPortable
  | .thread | .process | .device | .system => .isTrue trivial
  | .profileSpecific _ => .isFalse (fun h => h)

end MemoryScope

/--
The complete ordering declaration of one access.

Bundled so that an access cannot declare an order without a scope: the fields of
`OrderingDemand` are total, so an acquire with no stated scope is not
expressible. An unstated scope is not a claim a consistency profile could check.
-/
structure OrderingDemand where
  /-- Whether the access is atomic. -/
  atomicity : Atomicity := .nonAtomic
  /-- The ordering the access requests. -/
  order : MemoryOrder := .relaxed
  /-- The scope over which that ordering is claimed. -/
  scope : MemoryScope := .thread
deriving DecidableEq, Repr

namespace OrderingDemand

/-- The declaration carried by an ordinary single-threaded access. -/
def plain : OrderingDemand := {}

/--
`demand.IsPlain` holds when the access is non-atomic and relaxed.

The initial single-threaded profile admits only plain accesses
(`docs/MEMORY_MODEL.md` §9). Milestone M8 relaxes this; until then a profile
rejecting a non-plain demand is rejecting an unimplemented case rather than
modelling it as harmless.
-/
def IsPlain (demand : OrderingDemand) : Prop :=
  demand.atomicity = .nonAtomic ∧ demand.order = .relaxed

instance (demand : OrderingDemand) : Decidable demand.IsPlain :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem isPlain_plain : plain.IsPlain := ⟨rfl, rfl⟩

/-- Every part of a plain demand is portable, so a plain access is always
expressible against any profile. -/
theorem isPortable_of_isPlain {demand : OrderingDemand} (h : demand.IsPlain) :
    demand.order.IsPortable := by
  rw [h.2]
  trivial

end OrderingDemand

end Grass.Memory
