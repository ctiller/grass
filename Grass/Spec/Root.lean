import Grass.Semantics.SpecProcess
import Grass.Resource.Algebra
import Grass.Service.Domain

/-!
# The resource-indexed authoring root

`Grass.SpecRoot` (`Grass/Semantics/SpecProcess.lean`) is the unindexed
foundation-level record every certificate tier consumes. It is not what an
author writes: a spike's `Spec.lean` selects a resource value and states its
behavior relationally, over the portable `Grass.Service.Event` vocabulary
(`Grass/Service/Domain.lean`), not as a hand-built `RelationalSystem` and
`ObservationProjection` pair. `Grass.SpecProcess {R} [ResourceModel R]
(resources : R)` is that authoring root; `SpecProcess.root` recomputes the
exact `SpecRoot` the certificate chain consumes.

Liveness is not a `VerifiedProgram` field (`docs/VERIFIED_PROGRAM.md`,
decision 137): `LivenessDemand`s recorded by `SpecProcess.withLiveness` are
author theorem obligations proved against the specification, outside the
lowering certificate. `MeetsAllSpecificationTheorems` is exactly the
conjunction of those obligations.
-/

namespace Grass

open Resource

/-- A finite trace over `D` terminates when it ends with a call to one of
`D`'s own terminal requests. Per `Grass.Service.Domain.Terminal`'s contract,
no reply follows such a call, so an accepted trace never continues past it.
This is the generic, domain-agnostic reading of "the process ended": it names
no program-specific outcome, only the portable domain's own terminal law. -/
def Service.Event.Terminates {D : Service.Domain} (events : List (Service.Event D)) : Prop :=
  ∃ (lead : List (Service.Event D)) (request : D.Request),
    events = lead ++ [Service.Event.call request] ∧ D.Terminal request

/-- Environment assumptions an author's liveness theorem may lean on. Minimal
inventory for now — a single scheduler/platform responsiveness assumption;
growth is expected as later spikes need `stdinEventuallyEOF`-shaped or
GPU/scheduler-specific assumptions (`docs/TARGET_SEAMS.md`'s device seam). -/
inductive EnvironmentAssumption where
  | environmentResponsive
deriving DecidableEq, Repr

/-- An author-declared liveness demand. `terminatesUnder assumptions` records
that, assuming the named environment behaves as described, every trace the
specification accepts for an admitted input actually terminates. Growth is
expected: a later demand (progress, fairness, latency) extends this
inductive rather than folding into `terminatesUnder`. -/
inductive LivenessDemand where
  | terminatesUnder (assumptions : List EnvironmentAssumption)
deriving DecidableEq, Repr

/-- A relational behavior contract over one portable service domain's finite
event traces: which inputs are admitted, and, for each admitted input,
exactly which finite traces fulfil the contract. This is the shape every
domain-specific contract builder (`Console.writeLineContract`, and future
grammar/graphics analogues) targets. It is indexed by `resources` only so
`SpecProcess.ofRelational` composes directly with the resource-parameterized
certificate chain; no field here depends on the *value* of `resources`. -/
structure BehaviorContract {R : Type} [ResourceModel R] (resources : R) where
  /-- The specification's own input type (arguments, selected environment). -/
  Input : Type
  /-- The portable service vocabulary this contract's traces are drawn from. -/
  D : Service.Domain
  /-- Which inputs the specification takes responsibility for. -/
  admits : Input → Prop
  /-- Exactly the traces fulfilling the contract, for one admitted input. -/
  accepts : Input → List (Service.Event D) → Prop

/-- The precious resource-indexed specification an author writes. `contract`
is the relational behavior contract; `liveness` records author theorem
obligations declared outside the lowering certificate. -/
structure SpecProcess {R : Type} [ResourceModel R] (resources : R) where
  contract : BehaviorContract resources
  liveness : List LivenessDemand := []

namespace SpecProcess

variable {R : Type} [ResourceModel R] {resources : R}

/-- An empty portable demand family. A specification built directly from
`ofRelational` adds no lowering obligations of its own beyond the behavior
contract itself; a captured subprocess DSL (`Console.CapturedSpecification`)
may still extend a richer family the way it does today. -/
def emptyDemands : DemandFamily where
  Key := Empty
  keys := []
  complete := fun key => nomatch key
  unique := List.nodup_nil
  identity := fun key => nomatch key
  identityInjective := fun key => nomatch key
  kind := fun key => nomatch key
  statement := fun key => nomatch key

/-- The unindexed foundation root every certificate tier consumes. The
observation projection keeps every non-`silent` event
(`Grass.Service.Event.observable`), matching every specification-authoring
facade's contract (`Grass/Service/Domain.lean`). -/
def root (spec : SpecProcess resources) : SpecRoot where
  Input := spec.contract.Input
  AuditEvent := Service.Event spec.contract.D
  Observation := Service.Event spec.contract.D
  admits := spec.contract.admits
  observationProjection := ⟨Service.Event.observable⟩
  accepts := spec.contract.accepts
  requirements := emptyDemands

/-- Build a resource-indexed specification from a relational behavior
contract, with no author liveness demands yet declared. -/
def ofRelational (contract : BehaviorContract resources) : SpecProcess resources where
  contract := contract
  liveness := []

/-- Record one more author liveness demand. Append-only, matching
`Console.CapturedSpecification.withLiveness`. -/
def withLiveness (spec : SpecProcess resources) (demand : LivenessDemand) :
    SpecProcess resources :=
  { spec with liveness := spec.liveness ++ [demand] }

@[simp] theorem ofRelational_contract (contract : BehaviorContract resources) :
    (ofRelational contract).contract = contract := rfl

@[simp] theorem ofRelational_liveness (contract : BehaviorContract resources) :
    (ofRelational contract).liveness = [] := rfl

@[simp] theorem withLiveness_contract (spec : SpecProcess resources)
    (demand : LivenessDemand) : (spec.withLiveness demand).contract = spec.contract := rfl

@[simp] theorem withLiveness_liveness (spec : SpecProcess resources)
    (demand : LivenessDemand) :
    (spec.withLiveness demand).liveness = spec.liveness ++ [demand] := rfl

end SpecProcess

/-- The termination obligation of one liveness demand for one behavior
contract: every trace the contract accepts, for an admitted input, reaches
one of the domain's own terminal requests. `assumptions` records the
environment hypotheses the author is relying on; today every
`terminatesUnder` demand states this same obligation regardless of exactly
which assumptions are named; refining that per-assumption reading is
expected growth, not a soundness gap in what is proved here. -/
def LivenessDemand.obligation {R : Type} [ResourceModel R] {resources : R}
    (contract : BehaviorContract resources) : LivenessDemand → Prop
  | .terminatesUnder _assumptions =>
      ∀ input, contract.admits input →
        ∀ trace, contract.accepts input trace → Service.Event.Terminates trace

/-- The conjunction of every author-theorem obligation a specification's
declared liveness suite carries. This is the whole of the obligation family
for now: the resource-indexed root exports no other author-theorem kind yet.
Growth (progress, fairness, latency demands) extends this conjunction rather
than replacing it. -/
def MeetsAllSpecificationTheorems {R : Type} [ResourceModel R] {resources : R}
    (spec : SpecProcess resources) : Prop :=
  ∀ demand ∈ spec.liveness, demand.obligation spec.contract

end Grass
