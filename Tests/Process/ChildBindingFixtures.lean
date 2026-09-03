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

## Two bindings, because one of them cannot fail

`reflectsEveryAnswer` asks that every answer the parent could receive is one some
child outcome produces. At `.tick` it is cheap: the result type is `Unit`, so
"every answer" is one answer and a single `.succeeded` witness covers it.

An earlier version of this file said **no demand anywhere in the corpus has more
than one possible answer**, and filed that as owed work. A reviewer compiled the
refutation in one line: `Demand.log`'s result type is `Bool`, in the very file
this one imports. The law could have been asked a real question all along, and
the entry justified by that claim was wrong. §10.86.

`theLogBinding` asks it. What makes it more than an extra case is that the shape
is *forced*: `the_terminal_result_is_a_singleton` shows a `.succeeded` outcome carries
no information at this child — its terminal result is `ULift Unit` — so success
can supply at most one of the two answers, and `pendingDoesNotAnswer` forbids
pending supplying the other. The second answer has to come from a failure
outcome, and here it comes from a supervised death.
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
**A supervised death is named rather than discarded.**

`Drops` is the *name* for an outcome the parent never hears about, and this is
the first time it has been evaluated at one. An earlier version of this docstring
said `Drops` "stops a binding routing a failure to nothing at all", and a
reviewer pointed out it stops nothing: `ChildDemandBinding` has three laws and
none is about failure outcomes. What rules out silent discarding is that
`classify` is *total* — every outcome gets a disposition, and `routed_or_dropped`
says there is no third possibility. `Drops` records which choice was made.
§10.86.
-/
theorem death_is_named : theBinding.Drops (.died .supervised) := ⟨.detached, rfl⟩

/-! ## And one whose answer type is not a singleton -/

/--
**Success carries no information at this child.**

`countdownLifted.TerminalResult` is `ULift Unit`, and the terminality argument is
a proof, so every `.succeeded` outcome is the same outcome. This is why
`theLogBinding` below has to route a *failure* to an answer: with two answers to
reflect and only one success to reflect them with, `reflectsEveryAnswer` cannot
be satisfied from success alone.
-/
theorem the_terminal_result_is_a_singleton
    (left right : (baseRegistry.protocol theRequest.key).TerminalResult) : left = right := by
  obtain ⟨leftValue⟩ := left
  obtain ⟨rightValue⟩ := right
  cases leftValue
  cases rightValue
  rfl

/--
**A binding for a demand with two possible answers.**

`Demand.log`'s result type is `Bool`. Success answers `true`; a supervised death
answers `false`. Delete either and `reflectsEveryAnswer` fails, which is the
first time in this corpus that law has been able to.
-/
def theLogBinding :
    ChildDemandBinding (registry := baseRegistry) countdownLifted Demand.log theRequest where
  childExact := rfl
  childInitial := ⟨⟨0⟩, 0, [], rfl, rfl, rfl⟩
  classify := fun outcome =>
    match outcome with
    | .succeeded _ _ => .event (.result Demand.log true)
    | .pending => .event (.external .wake)
    | .interrupted _ => .nonReturning .abandoned
    | .faulted _ => .nonReturning .abandoned
    | .environmentViolation _ => .nonReturning .abandoned
    | .died _ => .event (.result Demand.log false)
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
    cases answer with
    | true => exact ⟨.succeeded ⟨()⟩ ⟨⟨0⟩, rfl⟩, rfl⟩
    | false => exact ⟨.died .supervised, rfl⟩

/-- Both answers really are produced, by different outcomes. -/
theorem both_answers_are_reachable :
    theLogBinding.classify (.succeeded ⟨()⟩ ⟨⟨0⟩, rfl⟩)
        = .event (.result Demand.log true) ∧
      theLogBinding.classify (.died .supervised) = .event (.result Demand.log false) :=
  ⟨rfl, rfl⟩

/-- And a death here is *not* a drop, which is the difference from `theBinding`. -/
theorem a_death_can_answer : ¬ theLogBinding.Drops (.died .supervised) := by
  rintro ⟨reason, routed⟩
  cases routed

end Grass.Process.Tests.ChildBinding
