import Grass.ISA.X86.Performance

/-!
# `Routable`, and the report that decides it

`Grass.ISA.X86.MicroarchProfile.unfusedSlotLowerBound` names `Routable` as a
precondition, and `unroutable` was written to report the uops that violate it.
`unroutable_eq_nil_iff` connects them. These check that the connection is the
one intended rather than a coincidence of two definitions that happen to agree
on the examples anyone tried.

Everything here is stated over an *arbitrary* profile, constrained only through
`portCount`. That is deliberate and not merely convenient: a fixture would need
a `Citation` and a `TimingBasis`, neither of which the property depends on, and
pinning a single profile would leave the theorems unable to distinguish "true of
profiles" from "true of this profile".
-/

namespace Tests.ISA.X86.Routable

open Grass.ISA.X86 Grass.ISA.X86.MicroarchProfile

/-- A uop with no eligible ports is unroutable on every profile, including one
with ports to spare. This is the case the two definitions reach by opposite
routes -- `List.all` is vacuously true on `[]`, and `Routable` asks for a member
of that same `[]` -- so it is the one worth pinning. -/
theorem empty_ports_never_routable (p : MicroarchProfile) (c : UopClass)
    (lat : Nat) : ¬ p.Routable [⟨c, [], lat⟩] := by
  intro h
  obtain ⟨_, hmem, _⟩ := h ⟨c, [], lat⟩ (by simp)
  exact absurd hmem (by simp)

/-- And `unroutable` reports exactly that uop, so the report is not silently
empty in the case that motivated it. -/
theorem empty_ports_reported (p : MicroarchProfile) (c : UopClass) (lat : Nat) :
    p.unroutable [⟨c, [], lat⟩] = [⟨c, [], lat⟩] := rfl

/-- A uop whose only port exists is routable. The `0 < p.portCount` hypothesis
is doing the work: without it the profile has no ports at all and the same uop
is unroutable, which is `out_of_range_not_routable` below. -/
theorem in_range_is_routable (p : MicroarchProfile) (c : UopClass) (lat : Nat)
    (h : 0 < p.portCount) : p.Routable [⟨c, [0], lat⟩] := by
  intro u hu
  simp only [List.mem_singleton] at hu
  subst hu
  exact ⟨0, by simp, h⟩

/-- A uop whose only eligible port does not exist on the profile is not
routable, and this is the case `unroutable` was written for: such a uop
contributes nothing to `portPressure`, so counting it would silently weaken the
bound. -/
theorem out_of_range_not_routable (p : MicroarchProfile) (c : UopClass)
    (lat : Nat) (id : PortId) (h : p.portCount ≤ id) :
    ¬ p.Routable [⟨c, [id], lat⟩] := by
  intro hr
  obtain ⟨j, hmem, hv⟩ := hr ⟨c, [id], lat⟩ (by simp)
  simp only [List.mem_singleton] at hmem
  subst hmem
  exact absurd hv (by simpa [MicroarchProfile.ValidPort] using h)

/-- A uop with a choice of ports is routable when *any* one of them exists, not
only when all do. A definition using `List.all` on the wrong side would make
this false. -/
theorem one_valid_port_suffices (p : MicroarchProfile) (c : UopClass)
    (lat : Nat) (h : 0 < p.portCount) :
    p.Routable [⟨c, [99, 0], lat⟩] := by
  intro u hu
  simp only [List.mem_singleton] at hu
  subst hu
  exact ⟨0, by simp, h⟩

/-- The empty uop list is routable: there is nothing to route. Worth stating
because `unfusedSlotLowerBound` has its own empty-list theorem, and a
precondition that failed vacuously there would make the pair inconsistent. -/
theorem nil_routable (p : MicroarchProfile) : p.Routable [] := by
  intro _ hu
  exact absurd hu (by simp)

end Tests.ISA.X86.Routable
