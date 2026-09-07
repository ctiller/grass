/-!
# Logical nominals and the monotone allocation history

`docs/FOUNDATION.md` law 22:

> No live-set freshness: process generations, channel epochs, child/message
> occurrences, and replacements are fresh over a monotone execution history;
> stale completions never regain authority after numeric reuse.

and `docs/PROCESS.md` §3:

> `usedNominals` contains every process generation, channel epoch, child demand,
> message occurrence, and coalesced replacement ever allocated in the execution
> prefix, including resolved/tombstoned identities. Freshness means absence from
> that monotone history, not merely absence from the current live set.

The law has two halves and this module owns only the first.

**Grass's own identities are never reissued.** That is `never_fresh_again`
below: an identity present in a history is not fresh in any history reachable
from it, however far the execution runs. It is a statement about the transitive
closure of extension, not about two particular histories differing, because the
failure mode law 22 names is a *late* completion — arbitrarily far in the
future — reacquiring authority.

**Externally reused numbers are paired with a generation.** An OS handle, a
socket slot, or an array index genuinely does recycle. `docs/MEMORY_MODEL.md`
and `Grass.Core` own that pairing; this module does not restate it. What this
module supplies is the nominal half of the pair, and `kind` is why a recycled
number in a new generation is a distinct identity rather than a coincidence:
a process generation and a channel epoch built from the same carrier value are
never equal.

## Why the history is finite

An earlier draft of `docs/PROCESS_IMPLEMENTATION_PLAN.md` made the history a
predicate `LogicalNominal -> Prop` on the grounds that an execution is
unbounded. That was wrong. An execution *prefix* is finite by construction: the
history starts empty and each transition adds finitely many nominals, so
unboundedness is a property of the limit and not of any value the union equation
in `docs/PROCESS.md` §3 ranges over. A predicate would make `historyExact` an
equality of predicates provable only through `funext` and `propext`, lose
decidability of freshness, and leave the occurrence-count resource axes of §5
with nothing to count.

## Custody note

`docs/PROCESS.md` §3 writes `Finset LogicalNominal`. Lean core has no `Finset`,
and `docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.2 records the decision not to add a
dependency for one. The representation here is a duplicate-free `List`; the
*interface* — membership, freshness as non-membership, and a union equation on
extension — is the normative one, so replacing the representation later changes
no consumer.
-/

namespace Grass.Process

universe u

/--
What kind of thing a nominal identifies.

`docs/PROCESS.md` §3 enumerates the allocation sites: process generations,
channel epochs, child demand occurrences, message occurrences, restart
identities, and coalesced replacements. Carrying the kind is what makes
identities of different kinds distinct even when their carrier values collide,
which is the property a driver's generation check relies on.
-/
inductive NominalKind
  /-- One incarnation of one process instance. -/
  | processGeneration
  /-- One session of one channel between two incarnations. -/
  | channelEpoch
  /-- One occurrence of a demand issued by one parent incarnation. -/
  | demandOccurrence
  /-- One message sent on one channel session. -/
  | messageOccurrence
  /-- The identity of a supervised restart. -/
  | restartIncarnation
  /-- The fresh occurrence a coalescing transition creates. -/
  | coalescedReplacement
  deriving DecidableEq, Repr

/--
A logical identity: a kind and a carrier value.

`Carrier` is a parameter rather than a fixed type because the mechanism that
makes carriers unrepeatable — a supply whose constructor is private — belongs to
`Grass.Core`, not here. This module proves what the *history* guarantees given
any carrier with decidable equality; `Grass.Core` proves that the carrier supply
never reissues.
-/
structure LogicalNominal (Carrier : Type u) where
  /-- Which allocation site produced this identity. -/
  kind : NominalKind
  /-- The identity itself. -/
  carrier : Carrier
  deriving DecidableEq, Repr

/--
The nominals allocated by one transition.

Duplicate-free, because a transition that claimed to allocate the same identity
twice has allocated it once and miscounted. `docs/PROCESS.md` §3 requires this
to be definitionally empty for non-allocating transitions, which is `empty`.
-/
structure Allocation (Carrier : Type u) where
  /-- The identities this transition creates. -/
  entries : List (LogicalNominal Carrier)
  /-- No identity is created twice by one transition. -/
  distinct : entries.Nodup

/--
Every nominal ever allocated in an execution prefix, including resolved and
tombstoned ones.
-/
structure NominalHistory (Carrier : Type u) where
  /-- The allocated identities, most recent first. Order carries no meaning. -/
  used : List (LogicalNominal Carrier)
  /-- Each identity appears once; the history records allocation, not use. -/
  distinct : used.Nodup

namespace Allocation

variable {Carrier : Type u}

/-- A transition that allocates nothing. -/
def empty : Allocation Carrier where
  entries := []
  distinct := List.nodup_nil

@[simp] theorem empty_entries : (empty : Allocation Carrier).entries = [] := rfl

end Allocation

namespace NominalHistory

variable {Carrier : Type u}

/-- The history before any transition. -/
def initial : NominalHistory Carrier where
  used := []
  distinct := List.nodup_nil

@[simp] theorem initial_used : (initial : NominalHistory Carrier).used = [] := rfl

/--
`nominal` has never been allocated in this prefix.

Non-membership in the *history*, not in a live set. That distinction is the
whole of law 22: a resolved occurrence remains in `used`, so its identity is
never fresh again and a late completion carrying it fails the check.
-/
def Fresh (history : NominalHistory Carrier)
    (nominal : LogicalNominal Carrier) : Prop :=
  nominal ∉ history.used

/-- An allocation is admissible when every identity it creates is fresh. -/
def Admissible (history : NominalHistory Carrier)
    (allocation : Allocation Carrier) : Prop :=
  ∀ nominal ∈ allocation.entries, history.Fresh nominal

/--
The history after a transition: the union of what was used and what was
allocated.

`docs/PROCESS.md` §3 states this as
`after.usedNominals = before.usedNominals ∪ transition.allocatedNominals`, and
`mem_extend` below is that equation. Concatenation is duplicate-free because
`admissible` says the two sides are disjoint.
-/
def extend (history : NominalHistory Carrier) (allocation : Allocation Carrier)
    (admissible : history.Admissible allocation) : NominalHistory Carrier where
  used := allocation.entries ++ history.used
  distinct := by
    refine List.nodup_append.mpr ⟨allocation.distinct, history.distinct, ?_⟩
    intro a inAllocation b inHistory equal
    exact admissible a inAllocation (equal ▸ inHistory)

/-- The union equation of `docs/PROCESS.md` §3. -/
@[simp] theorem mem_extend {history : NominalHistory Carrier}
    {allocation : Allocation Carrier}
    {admissible : history.Admissible allocation}
    {nominal : LogicalNominal Carrier} :
    nominal ∈ (history.extend allocation admissible).used ↔
      nominal ∈ allocation.entries ∨ nominal ∈ history.used :=
  List.mem_append

/-- Extending with an empty allocation changes nothing. -/
@[simp] theorem extend_empty (history : NominalHistory Carrier)
    (admissible : history.Admissible Allocation.empty) :
    history.extend Allocation.empty admissible = history := by
  cases history; rfl

/--
`Reaches before after` holds when `after` is `before` after some number of
admissible extensions.

This is the relation an execution actually establishes, and it is what
`never_fresh_again` is stated over. Stating monotonicity between two adjacent
histories would prove far less than law 22 needs.
-/
inductive Reaches : NominalHistory Carrier → NominalHistory Carrier → Prop
  | refl (history : NominalHistory Carrier) : Reaches history history
  | extend {start middle : NominalHistory Carrier}
      (prior : Reaches start middle) (allocation : Allocation Carrier)
      (admissible : middle.Admissible allocation) :
      Reaches start (middle.extend allocation admissible)

/-- The history only grows. -/
theorem mem_of_reaches {start finish : NominalHistory Carrier}
    (reaches : Reaches start finish) {nominal : LogicalNominal Carrier}
    (used : nominal ∈ start.used) : nominal ∈ finish.used := by
  induction reaches with
  | refl => exact used
  | extend _ _ _ ih => exact List.mem_append.mpr (Or.inr ih)

/--
**Law 22.** An identity allocated in an execution prefix is never fresh again,
in any history that prefix reaches.

Not "not fresh in the next history": a stale completion arrives late, so the
claim has to hold at unbounded distance. This is the theorem that makes a
generation or epoch check sound, and it is why the history retains resolved and
tombstoned identities instead of removing them when they die.
-/
theorem never_fresh_again {start finish : NominalHistory Carrier}
    (reaches : Reaches start finish) {nominal : LogicalNominal Carrier}
    (used : nominal ∈ start.used) : ¬ finish.Fresh nominal :=
  fun stale => stale (mem_of_reaches reaches used)

/--
An allocation admissible at a later history was admissible at every earlier one.

The useful direction of monotonicity for a driver proof: freshness is only ever
harder to establish as the execution runs, so a freshness fact proved once at
allocation time is not invalidated by anything that happens afterwards.
-/
theorem admissible_of_reaches {start finish : NominalHistory Carrier}
    (reaches : Reaches start finish) {allocation : Allocation Carrier}
    (admissible : finish.Admissible allocation) : start.Admissible allocation :=
  fun nominal member used => admissible nominal member (mem_of_reaches reaches used)

/--
Identities of different kinds are distinct even at the same carrier value.

A driver that recycles a numeric slot across a process generation and a channel
epoch cannot produce a collision by accident; it has to produce one deliberately
by reusing the carrier at the same kind, which `Admissible` then rejects.
-/
theorem kind_separates {Carrier : Type u} {carrier : Carrier}
    {left right : NominalKind} (different : left ≠ right) :
    (⟨left, carrier⟩ : LogicalNominal Carrier) ≠ ⟨right, carrier⟩ :=
  fun equal => different (congrArg LogicalNominal.kind equal)

end NominalHistory

end Grass.Process
