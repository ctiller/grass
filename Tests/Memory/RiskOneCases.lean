import Tests.Memory.Spike1Reference

/-!
# The two pre-freeze cases risk 1 names and nothing exercised

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §9 risk 1 lists five instruction shapes that
must be expressed as M1 fixtures before the descriptor is frozen, on the grounds
that a seam tested only against instructions it was designed for has not been
tested. Three existed: a divide fault between two memory effects (`divMem`), an
implicit-stack operation (`pushR12`), and a misaligned crossing access
(`splitPageStore`). Two did not — a repeated string operation and a locked
read-modify-write — and both appear in the acceptance corpus:
`Spikes/2_Sort/Assembly.lean` uses `rep movsb`, `Spikes/3_Gzip/Assembly.lean` uses
`rep stosw`, and §3.13 records `lock cmpxchg16b` as the case it was unsure of.

Review found the absence while checking the plan's exit criteria against the tree.
This file is those two cases, and the point of writing them is to find out what the
frozen shape cannot say. Both findings are recorded below and in §4.2 rather than
hidden by a fixture shaped to pass.

## What `rep movsb` needs, and what it costs

The count is a runtime register. `AccessDescriptor.range` is a fixed `ByteRange`, so
one descriptor describes one count — which is not a defect, because
`HasOperationFacets.facets` maps an *operation value* to its facets and an operation
value is what a decoder produces after operands are resolved. So the model is a
family: `repMovsb count` is a different operation for each count, and `substeps` is a
function of it.

The cost is real and worth stating. A proof about `rep movsb` for all counts is a
proof about that family, not about one descriptor, so every `decide`-based side
condition in the `Tests/Memory/Spike1Block.lean` idiom stops working and an induction
takes its place. The zero case is a separate branch — `SubstepSequence.none_`, no
access at all — which an ISA model must remember to write.

## What `lock cmpxchg16b` needs

One sixteen-byte atomic read-modify-write, aligned to sixteen. §3.13 said this case
"still cannot declare its compare and swap operands", and that turns out to be a
statement about *values*, which this layer does not model: the comparand and the
replacement live in registers, and what memory sees is a read of sixteen bytes and a
conditional write of sixteen bytes. The descriptor says that.

What it cannot say is the *conditional*: `AccessDescriptor.intent` declares
`writes := true` and there is no way to express "writes only if the comparison
succeeded". The commit-prefix model has `Committed`, which is about how many bytes a
*faulting* access wrote, not about a write that lawfully did not happen. So the
model over-approximates: a failed compare-and-swap is described as a write. That is
the safe direction for authority — it demands write authority it may not use — and
the wrong direction for a race argument, where a non-writing access does not conflict.
Recorded in §4.2.
-/

namespace Grass.Tests.RiskOne

open Grass.Core Grass.Memory Grass.Tests.Spike1

/-! ## A repeated string operation -/

/-- The source buffer `rep movsb` reads. -/
def sourceProvenance : Provenance :=
  { space := .cpuVirtual, root := stackAlloc, epoch := epoch₀
    source := .stack, rootExtent := ⟨0, 4096⟩
    path := [{ kind := .slot, label := ⟨"source"⟩, extent := ⟨1024, 1024⟩ }] }

/-- The destination buffer it writes. Disjoint from the source, which is the case a
profile must require: overlapping `rep movsb` is direction-flag dependent and
`docs/MEMORY_MODEL.md` says nothing about it. -/
def destinationProvenance : Provenance :=
  { space := .cpuVirtual, root := stackAlloc, epoch := epoch₀
    source := .stack, rootExtent := ⟨0, 4096⟩
    path := [{ kind := .slot, label := ⟨"destination"⟩, extent := ⟨2048, 1024⟩ }] }

/--
`rep movsb` with `rcx = count`.

Two accesses: the whole source range is read, then the whole destination range is
written. **Not** `count` pairs of one-byte accesses — the instruction's memory effect
is the transfer, and `docs/MEMORY_MODEL.md` §1's commit-prefix model is what carries
partial progress, so a fault partway is a committed prefix of these two rather than a
different number of substeps.

`priorEffectsVisible`: if the write faults, the read has happened. That is the
default on x86-64 and it is declared rather than assumed.
-/
def repMovsb (count : Nat) : SubstepSequence :=
  if count = 0 then .none_
  else
    { substeps :=
        [ .access (access sourceProvenance ⟨1024, count⟩ 0x1400 .read .readWrite 1
            true false),
          .access (access destinationProvenance ⟨2048, count⟩ 0x1800 .write .readWrite 1
            false true) ]
      onFault := .priorEffectsVisible }

/-- **A count of zero is a different sequence, not a degenerate one.**

`AccessDescriptor.WellFormedIn.rangeNonEmpty` refuses an access naming no bytes, so a
zero-count `rep movsb` cannot be modelled as two empty accesses. It has no memory
effect at all, and an ISA model must case-split to say so. This is the branch the
plan's §4.2 note about `rangeNonEmpty` was written for. -/
theorem zero_count_touches_nothing :
    (repMovsb 0).accesses = ([] : List AccessDescriptor) := by decide

/-- A nonzero count is two accesses, and they are well formed. -/
theorem a_nonzero_count_is_two_accesses :
    (repMovsb 8).substeps.length = 2 ∧ (repMovsb 8).WellFormedIn spaceTable := by
  exact ⟨by decide, by decide⟩

/-- **The same holds at every count the fixture can reach**, which is the point of
writing it as a family: a proof about `rep movsb` is a proof about all counts, and
this is that proof for the bounded case a `decide` can close. An unbounded one is an
induction, which is the cost §9 risk 1 wanted measured. -/
theorem every_small_count_is_well_formed :
    ∀ n, n < 64 → (repMovsb (n + 1)).WellFormedIn spaceTable := by decide

/-- The read happens before the write, and survives a fault on the write. The fact
`docs/MEMORY_MODEL.md` §1 forbids assuming away. -/
theorem the_read_survives_a_write_fault :
    (repMovsb 8).visibleEffects? 1 =
      some [access sourceProvenance ⟨1024, 8⟩ 0x1400 .read .readWrite 1 true false] :=
  rfl

/-- Source and destination are the same storage and disjoint ranges, so a framing
argument must separate them by range. Overlapping `rep movsb` is a different
instruction semantically and this fixture does not model it. -/
theorem source_and_destination_do_not_overlap :
    sourceProvenance.SameStorage destinationProvenance ∧
    (ByteRange.mk 1024 1024).Disjoint ⟨2048, 1024⟩ := by
  exact ⟨⟨rfl, rfl, rfl⟩, by decide⟩

/-! ## A locked read-modify-write -/

/-- The sixteen-byte aligned word `lock cmpxchg16b` operates on. -/
def lockedWordProvenance : Provenance :=
  { space := .cpuVirtual, root := stackAlloc, epoch := epoch₀
    source := .stack, rootExtent := ⟨0, 4096⟩
    path := [{ kind := .slot, label := ⟨"lockedWord"⟩, extent := ⟨3072, 16⟩ }] }

/--
`lock cmpxchg16b [mem]`.

One access: sixteen bytes, read and written, atomic, aligned to sixteen. The
comparand and replacement are register values and are not this layer's; what memory
sees is the read and the conditional write.
-/
def lockCmpxchg16b : SubstepSequence :=
  .single
    { access lockedWordProvenance ⟨3072, 16⟩ 0x1C00 .atomicReadWrite .readWrite 16
        true true with
      ordering := { atomicity := .atomic, order := .sequentiallyConsistent } }

/-- It is well formed, which is the answer §3.13 was unsure of: the descriptor can
say a sixteen-byte aligned atomic read-modify-write. -/
theorem the_locked_rmw_is_well_formed :
    lockCmpxchg16b.WellFormedIn spaceTable := by decide

/-- **It reads and writes in one access**, which is why `AccessIntent` is a set of
capabilities rather than a tag: collapsing this to "write" would lose the read the
consistency model has to account for. -/
theorem the_locked_rmw_is_both :
    ∀ d ∈ lockCmpxchg16b.accesses,
      d.intent.reads = true ∧ d.intent.writes = true ∧ d.intent.isAtomic = true := by
  decide

/-- Its atomicity and its ordering agree, which `WellFormedIn.atomicityAgrees`
requires — an access cannot claim to be atomic while declaring a non-atomic
ordering. -/
theorem the_locked_rmw_declares_its_ordering :
    ∀ d ∈ lockCmpxchg16b.accesses,
      d.ordering.atomicity = .atomic ∧ d.ordering.order = .sequentiallyConsistent := by
  decide

/--
**What the descriptor cannot say: that the write is conditional.**

`intent.writes` is `true`, and a compare-and-swap whose comparison fails writes
nothing. There is no field for "writes only if a condition held" —
`Committed` is about how many bytes a *faulting* access wrote, which is a different
question. So a failed CAS is described as a write.

That is the safe direction for authority: the access demands write authority it may
not use, and demanding more than needed refuses more than needed. It is the wrong
direction for `docs/MEMORY_MODEL.md` §7.3's conflict rule, where an access that does
not write does not conflict — so a profile's race argument over `lock cmpxchg16b`
will over-approximate. Recorded in §4.2 rather than papered over; this theorem is the
gap, stated.
-/
theorem the_failed_compare_is_indistinguishable :
    ∀ d ∈ lockCmpxchg16b.accesses, d.intent.writes = true := by decide

end Grass.Tests.RiskOne
