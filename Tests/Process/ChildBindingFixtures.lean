import Grass.Process.Network.Child
import Tests.Process.M1Fixtures

/-!
# A parent demand bound to a child protocol

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.86. `ChildDemandBinding` carries seven
fields, five of them Props, and an emptiness sweep found it constructed nowhere.
So `successAnswersThisDemand`, `pendingDoesNotAnswer` and `reflectsEveryAnswer`
were claims about a relation with no inhabitants, and `Drops` — the predicate
that says an outcome was named non-returning rather than silently discarded — had
never been evaluated.

`theBinding` binds the countdown's `.tick` to a registered child run of the same
protocol, and `death_is_named` shows a supervised death routed to
`NonReturningReason.detached` rather than dropped.

## What this witness does *not* test, and cannot

`reflectsEveryAnswer` asks that every answer the parent could receive is one some
child outcome produces. It is cheap here, and it is cheap for the same reason at
every fixture in this corpus: `.tick`'s result type is `Unit`, so "every answer"
is one answer, and a single `.succeeded` witness covers it. **No demand anywhere
in the corpus has more than one possible answer**, so the law has never been
asked a question it could fail. `Tests/Process/RichAcceptanceFixtures.lean` made
the same observation about acceptance and answered it by building a richer
vocabulary; the same is owed here. §10.86 records it.
-/

namespace Grass.Process.Tests.ChildBinding

open Grass.Process
open Grass.Process.Tests

/-- The child run this binding authorizes: a countdown of zero. -/
def theRequest : ChildRequest baseRegistry where
  key := ()
  request := ⟨0⟩

/--
**A parent demand realized by a registered child protocol.**

The corpus's first `ChildDemandBinding`. Every outcome is routed: success answers
the demand, pending wakes the parent without answering, and the four failures are
named non-returning rather than dropped.
-/
def theBinding :
    ChildDemandBinding (registry := baseRegistry) countdownLifted Demand.tick theRequest where
  childExact := rfl
  childInitial := ⟨⟨0⟩, 0, [], rfl, rfl, rfl⟩
  classify := fun outcome =>
    match outcome with
    | .succeeded _ _ => .event (.result Demand.tick ())
    | .pending => .event (.external .wake)
    | .interrupted _ => .nonReturning .abandoned
    | .faulted _ => .nonReturning .abandoned
    | .environmentViolation _ => .nonReturning .abandoned
    | .died _ => .nonReturning .detached
  successAnswersThisDemand := by
    intro result isTerminal event routed
    cases routed
    rfl
  pendingDoesNotAnswer := by
    intro event routed
    cases routed
    rfl
  reflectsEveryAnswer := by
    intro answer
    refine ⟨.succeeded ⟨()⟩ ⟨⟨0⟩, rfl⟩, ?_⟩
    cases answer
    rfl

/--
**It drops nothing silently: a supervised death is named.**

`Drops` is what stops a binding routing a failure to nothing at all, and this is
the first time it has been evaluated at an outcome.
-/
theorem death_is_named : theBinding.Drops (.died .supervised) := ⟨.detached, rfl⟩

end Grass.Process.Tests.ChildBinding
