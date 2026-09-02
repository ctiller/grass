import Grass.Memory.AddressSpace
import Grass.Memory.Range

/-!
# From offsets to addresses

`Grass/Memory/Range.lean` reasons about offsets in `Nat`, and says why: an offset
is bounded by its allocation's size rather than the machine word, and `Nat` keeps
every framing proof free of wraparound. It also records the debt that choice
creates —

> `Nat` disjointness does not by itself imply non-aliasing of the corresponding
> machine addresses.

— and names `WithinBound` as the predicate that pays it. This module is the
payment. Without it, every framing lemma in the memory layer proves something
about offsets that nothing connects to memory.

The condition is `FitsAllocation`: the allocation's own bytes do not wrap the
address space. That is not a modelling convenience. An allocation whose last byte
wraps past `2^64` has two distinct offsets at one address, so *no* disjointness
argument about it could be sound, and a profile admitting one has already lost.
`docs/MEMORY_MODEL.md` §2 makes provenance rather than address the authority
precisely so that this is the only place the arithmetic has to be checked.
-/

namespace Grass.Memory

/-- The machine address of an offset within an allocation based at `base`. -/
def addressOf (base : MachineAddress) (offset : Nat) : MachineAddress :=
  base + BitVec.ofNat 64 offset

/--
`FitsAllocation base size` holds when an allocation of `size` bytes based at
`base` does not wrap the address space.

The hypothesis every bridge lemma below needs, and the one a profile owes for each
allocation it admits.
-/
def FitsAllocation (base : MachineAddress) (size : Nat) : Prop :=
  base.toNat + size ≤ 2 ^ 64

instance (base : MachineAddress) (size : Nat) : Decidable (FitsAllocation base size) :=
  inferInstanceAs (Decidable (_ ≤ _))

@[simp] theorem addressOf_zero (base : MachineAddress) : addressOf base 0 = base := by
  simp [addressOf]

/-- Inside a non-wrapping allocation, an offset's address is its base plus the
offset, with no reduction. This is the fact every other lemma here rests on. -/
theorem toNat_addressOf {base : MachineAddress} {size : Nat}
    (hfits : FitsAllocation base size) {offset : Nat} (hlt : offset < size) :
    (addressOf base offset).toNat = base.toNat + offset := by
  have hbound : base.toNat + offset < 2 ^ 64 := by
    rw [FitsAllocation] at hfits
    omega
  simp only [addressOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : offset < 2 ^ 64)]
  exact Nat.mod_eq_of_lt hbound

/--
**Distinct offsets in a non-wrapping allocation have distinct addresses.**

The injectivity the offset-based framing lemmas assume and could not state.
-/
theorem addressOf_injective {base : MachineAddress} {size : Nat}
    (hfits : FitsAllocation base size) {i j : Nat} (hi : i < size) (hj : j < size)
    (hne : i ≠ j) : addressOf base i ≠ addressOf base j := by
  intro heq
  have hti := toNat_addressOf hfits hi
  have htj := toNat_addressOf hfits hj
  rw [heq] at hti
  omega

/--
**Disjoint ranges do not alias.**

The bridge `Grass/Memory/Range.lean` names as owed. Given an allocation that does
not wrap, two disjoint offset ranges within it cover disjoint sets of machine
addresses — so a write confined to one leaves every byte of the other alone, at
the machine level and not merely in `Nat`.
-/
theorem disjoint_ranges_do_not_alias {base : MachineAddress} {size : Nat}
    (hfits : FitsAllocation base size) {r s : ByteRange}
    (hr : r.WithinBound size) (hs : s.WithinBound size) (hd : r.Disjoint s)
    {i j : Nat} (hi : r.Covers i) (hj : s.Covers j) :
    addressOf base i ≠ addressOf base j := by
  have hine : i ≠ j := by
    intro heq
    exact hd.not_covers hi (heq ▸ hj)
  refine addressOf_injective hfits ?_ ?_ hine
  · rw [ByteRange.covers_def] at hi
    rw [ByteRange.withinBound_def] at hr
    omega
  · rw [ByteRange.covers_def] at hj
    rw [ByteRange.withinBound_def] at hs
    omega

/--
The converse direction, which is the one a framing proof actually uses: if two
addresses within a non-wrapping allocation are equal, the offsets were equal.
-/
theorem offset_eq_of_addressOf_eq {base : MachineAddress} {size : Nat}
    (hfits : FitsAllocation base size) {i j : Nat} (hi : i < size) (hj : j < size)
    (heq : addressOf base i = addressOf base j) : i = j := by
  by_cases hne : i = j
  · exact hne
  · exact absurd heq (addressOf_injective hfits hi hj hne)

/--
Two allocations that do not overlap in the address space share no address.

`docs/MEMORY_MODEL.md` §2 makes provenance the authority, so this is *not* how
distinct allocations are told apart — distinct `AllocId`s already are distinct.
It is what a profile needs to justify placing two allocations at addresses that
do not collide, which is a placement fact rather than a provenance one.
-/
theorem distinct_allocations_do_not_alias {baseA baseB : MachineAddress}
    {sizeA sizeB : Nat} (hfitsA : FitsAllocation baseA sizeA)
    (hfitsB : FitsAllocation baseB sizeB)
    (hapart : baseA.toNat + sizeA ≤ baseB.toNat ∨ baseB.toNat + sizeB ≤ baseA.toNat)
    {i j : Nat} (hi : i < sizeA) (hj : j < sizeB) :
    addressOf baseA i ≠ addressOf baseB j := by
  intro heq
  have hti := toNat_addressOf hfitsA hi
  have htj := toNat_addressOf hfitsB hj
  rw [heq] at hti
  omega

end Grass.Memory
