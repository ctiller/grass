import Grass.Core.Context
import Grass.Core.Name
import Grass.Obligation.Core

/-!
# Terminal dispositions

`docs/OBLIGATIONS.md` §3 fixes exactly five dispositions an obligation may have
at a terminal edge, and requires every obligation to have one. `docs/FOUNDATION.md`
law 7 states the same rule negatively: no obligation disappearance.

The list is closed. That is a deliberate difference from the open nominal kinds
elsewhere in this layer: a new protocol may invent a new kind of duty, but it may
not invent a new way for a duty to end without renewed review, because the
disposition is precisely what the terminal theorem must map onto a declared
program result.

`abandonedUnknown` is the one to read carefully. It records that failure permitted
loss of knowledge, and §3 requires that loss to be "explicitly reflected in the
program result/specification". A platform profile's permission to abandon does not
by itself prove the program reports the abandonment; that connection is the M5
terminal theorem's burden, and nothing here should be read as discharging it.
-/

namespace Grass.Obligation

open Grass.Core

/--
How one obligation ended at a terminal edge.

Exactly the five dispositions of `docs/OBLIGATIONS.md` §3.
-/
inductive Disposition where
  /-- The required action occurred. -/
  | discharged
  /-- A named live owner accepted responsibility. -/
  | transferred (newOwner : ContextId)
  /-- The OS or runtime teardown contract assumed it. -/
  | teardownAdopted (contract : Name)
  /-- The protocol's failure branch was performed. -/
  | aborted
  /-- Failure permitted loss of knowledge, which the specification must report. -/
  | abandonedUnknown
deriving DecidableEq, Repr

namespace Disposition

/--
`d.IsNormal` holds when `d` ended the obligation in good standing.

`docs/OBLIGATIONS.md` §3: "Successful exit must not leave external obligations in
an abnormal disposition." This predicate names the side of that rule an exit
theorem must establish; it does not decide which obligations are external, which
is a profile fact.
-/
def IsNormal : Disposition → Prop
  | .discharged | .transferred _ | .teardownAdopted _ => True
  | .aborted | .abandonedUnknown => False

instance : (d : Disposition) → Decidable d.IsNormal
  | .discharged | .transferred _ | .teardownAdopted _ => .isTrue trivial
  | .aborted | .abandonedUnknown => .isFalse (fun h => h)

/--
`d.RequiresSpecificationSupport` holds when `d` is admissible only if the
program's own specification accepts that outcome.

§3 permits `aborted` and `abandonedUnknown` on failure "only when its
specification accepts that outcome", so these two are exactly the cases the M5
terminal theorem must check against the declared result rather than against the
platform profile alone.
-/
def RequiresSpecificationSupport : Disposition → Prop
  | .aborted | .abandonedUnknown => True
  | _ => False

instance : (d : Disposition) → Decidable d.RequiresSpecificationSupport
  | .aborted | .abandonedUnknown => .isTrue trivial
  | .discharged | .transferred _ | .teardownAdopted _ => .isFalse (fun h => h)

@[simp] theorem isNormal_discharged : IsNormal .discharged := trivial

@[simp] theorem not_isNormal_abandonedUnknown : ¬ IsNormal .abandonedUnknown := fun h => h

@[simp] theorem not_isNormal_aborted : ¬ IsNormal .aborted := fun h => h

/-- The two classifications are exactly complementary: an abnormal disposition is
precisely one the specification must license. -/
theorem requiresSpecificationSupport_iff_not_isNormal (d : Disposition) :
    d.RequiresSpecificationSupport ↔ ¬ d.IsNormal := by
  cases d <;> simp [RequiresSpecificationSupport, IsNormal]

end Disposition

/--
One obligation's terminal outcome: which obligation, and how it ended.

Keyed by identity rather than by the obligation value. An earlier version of this
sentence gave the reason as "`Obligation` has an existential payload and no
equality", and both halves are false: it derives `DecidableEq`, and
`Grass/Obligation/Core.lean`'s own module comment says the existential deliberately
does *not* live there. Review compiled `example : DecidableEq Obligation :=
inferInstance` against this tree.

Identity is still the right key, for a reason that survives: `LedgerDelta.transfer`
changes a duty's owner while it stays the same duty, so an accounting keyed on the
value would treat one obligation as two.
-/
structure TerminalOutcome where
  /-- Which obligation this outcome accounts for. -/
  obligation : ObligationId
  /-- How it ended. -/
  disposition : Disposition
deriving DecidableEq, Repr

end Grass.Obligation
