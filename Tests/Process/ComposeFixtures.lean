import Grass.Process.Cancellation.Compose

/-!
# `uncancellable |> cancelpoint |> uncancellable`

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §5's exit criterion asks for
`docs/PROCESS.md` §3's worked example to *be a theorem*. This file is that.

§3 asserts four things about the example, and each is a theorem below:

1. "A request arriving in the first region is retained until the middle point."
   — `request_in_the_first_region_waits_for_the_point`.
2. "A request arriving after that point is retained until the process's terminal
   boundary." — `request_after_the_point_reaches_the_boundary`.
3. "A bounded-cancellation claim therefore also needs the two uncancellable
   regions to terminate within named bounds." — `bounded_example_is_cancellable`
   holds only for the bounded variant.
4. "A forever-blocking uncancellable region cannot acquire eventual cancellation
   merely by being sequenced with a later point." —
   `blocking_first_region_defeats_the_point`, which is the same three-region
   shape with one bound removed.

The fourth is the one that would be easy to get wrong and impossible to notice:
an author who writes the shape without the bounds gets a composite that *looks*
cancellable — it plainly contains a cancellation point — and is not.
-/

namespace Grass.Process.Tests.Compose

open Grass.Process
open Grass.Process.CancellationSequence

/-! ## The three regions -/

/-- The first region: uncancellable, and it ends within ten steps. -/
def firstRegion : CancellationRegion := ⟨.uncancellable, some 10⟩

/-- The middle: a declared cancellation point. -/
def middlePoint : CancellationRegion := ⟨.cancellationPoint, some 1⟩

/-- The third: uncancellable again, bounded. -/
def lastRegion : CancellationRegion := ⟨.uncancellable, some 5⟩

/-- The same first region, but able to block forever. -/
def blockingFirstRegion : CancellationRegion := ⟨.uncancellable, none⟩

/-! ## The example, built with `|>` -/

/-- `uncancellable |> cancelpoint |> uncancellable`, bounded throughout. -/
def workedExample : CancellationSequence :=
  (one firstRegion).seq ((one middlePoint).seq (one lastRegion))

/-- The same shape, with the first region able to block forever. -/
def blockingExample : CancellationSequence :=
  (one blockingFirstRegion).seq ((one middlePoint).seq (one lastRegion))

/--
Bracketing does not matter, which is what `seq_assoc` is for.

Worth stating at the example rather than only in general: `|>` is written
infix and left-associating in the corpus, and a reader should be able to see
that the two readings are the same object here.
-/
theorem bracketing_does_not_matter :
    ((one firstRegion).seq (one middlePoint)).seq (one lastRegion) = workedExample :=
  seq_assoc _ _ _

/-- It is the three regions in order. -/
theorem workedExample_regions :
    workedExample.regions = [firstRegion, middlePoint, lastRegion] := rfl

/-! ## §3's four assertions -/

/--
**1. A request arriving in the first region is retained until the middle point.**

`resolvedFrom 0` is the middle region's index, not the first's: the first region
is uncancellable, so it latches the request rather than acting on it.
-/
theorem request_in_the_first_region_waits_for_the_point :
    workedExample.resolvedFrom 0 = some 1 := rfl

/-- And a request arriving *at* the point is acted on there. -/
theorem request_at_the_point_is_acted_on :
    workedExample.resolvedFrom 1 = some 1 := rfl

/--
**2. A request arriving after that point is retained until the terminal
boundary.**

`none` is that boundary. The third region is uncancellable and nothing follows
it, so §3's "the ordinary terminal disposition must classify it" is the only
remaining answer — and this theorem is what says there is no other.
-/
theorem request_after_the_point_reaches_the_boundary :
    workedExample.resolvedFrom 2 = none := rfl

/-- Every arrival has one of those two fates and no third. -/
theorem every_request_is_accounted_for (arrival : Nat) :
    (∃ index, workedExample.resolvedFrom arrival = some index) ∨
      workedExample.resolvedFrom arrival = none :=
  workedExample.request_is_latched_or_acted_on arrival

/--
**3. With both uncancellable regions bounded, the example is eventually
cancellable.**

Both halves: there is a point that acts on a request, and no region can delay
reaching it forever.
-/
theorem bounded_example_is_cancellable : workedExample.EventuallyCancellable := by
  refine ⟨⟨middlePoint, ?_, rfl⟩, ?_⟩
  · rw [workedExample_regions]
    simp
  · intro region present
    rw [workedExample_regions] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl <;>
      simp [CancellationRegion.Bounded, firstRegion, middlePoint, lastRegion]

/--
**4. A forever-blocking first region defeats the claim, point or no point.**

§3's closing sentence, and the theorem this whole module exists for.
`blockingExample` still contains the very same cancellation point —
`blocking_example_still_has_a_point` says so — and is still not eventually
cancellable, because a request arriving in the first region may never reach it.

An author who writes the three-region shape and forgets the bounds gets exactly
this: something that looks cancellable and is not.
-/
theorem blocking_example_still_has_a_point :
    blockingExample.HasCancellationPoint :=
  ⟨middlePoint, by simp [blockingExample, seq, one], rfl⟩

theorem blocking_first_region_defeats_the_point :
    ¬ blockingExample.EventuallyCancellable :=
  unbounded_region_defeats_cancellation
    (region := blockingFirstRegion)
    (by simp [blockingExample, seq, one])
    ⟨rfl, rfl⟩

/--
And sequencing more bounded work after it does not repair the claim.

The operator-level version: whatever you compose onto a forever-blocking region,
the result is still not eventually cancellable. This is what stops `|>` from
being a composition that manufactures a guarantee out of two things that did not
have one.
-/
theorem no_amount_of_later_work_repairs_it (more : CancellationSequence) :
    ¬ (blockingExample.seq more).EventuallyCancellable :=
  seq_inherits_unboundedness
    (region := blockingFirstRegion)
    (Or.inl (by simp [blockingExample, seq, one]))
    ⟨rfl, rfl⟩

/-! ## What "eventually cancellable" does not mean -/

/--
A point followed by a bounded uncancellable tail.

`docs/PROCESS.md` §3's worked example, minus the leading region: a request
arriving in the point is acted on, and a request arriving in the tail is
retained to the terminal boundary.
-/
def pointThenTail : CancellationSequence :=
  ⟨[⟨.cancellationPoint, some 1⟩, ⟨.uncancellable, some 1⟩]⟩

/-- It is eventually cancellable: it has a point, and its uncancellable region
promises to end. -/
theorem the_tail_is_cancellable : pointThenTail.EventuallyCancellable := by
  refine ⟨⟨⟨.cancellationPoint, some 1⟩, by simp [pointThenTail], rfl⟩, ?_⟩
  intro region present uncancellable
  simp only [pointThenTail, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact absurd uncancellable (by decide)
  · show (some 1 : Option Nat) ≠ none
    intro equal
    cases equal

/--
**And a request arriving after the point is never acted on.**

`resolvedFrom 1 = none`: from the tail onward there is no region that may act, so
the request is latched to the process's terminal boundary.
-/
theorem a_late_request_is_never_acted_on : pointThenTail.resolvedFrom 1 = none := rfl

/--
**So "eventually cancellable" does not mean every request is acted on.**

The two together, and the reason `EventuallyCancellable`'s docstring was
corrected: a reader who takes the name at face value will be wrong about exactly
this composite. §3 is explicit that the late request is *retained*, and
`request_is_latched_or_acted_on` is the law 7 statement that retention and action
are the only two answers.

Local adversarial review built this; the definition was right and the sentence
above it was not.
-/
theorem cancellable_yet_latched :
    pointThenTail.EventuallyCancellable ∧ pointThenTail.resolvedFrom 1 = none :=
  ⟨the_tail_is_cancellable, a_late_request_is_never_acted_on⟩


end Grass.Process.Tests.Compose
