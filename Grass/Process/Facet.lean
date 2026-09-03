import Grass.Process.Correct
import Grass.Process.Termination

/-!
# Termination facets

`docs/PROCESS.md` §3 attaches a facet only when a process makes a promise:

> This sophistication is capability-driven. `ProcessCorrect` itself retains only
> ordinary invariant, terminal, observation, demand, and progress facts. A
> process plan attaches `TerminationFacet` only when the process exports a
> cancellation/restart/upgrade promise or another component relies on one. The
> ordinary facet is derived from the existing terminal/lifecycle proof. Pure
> serial functions, straight-line helpers, and uncancellable leaf processes gain
> no new author obligation.

Two sentences there are claims a type can keep, and this module exists to make
both checkable rather than conventional.

## "Pure serial functions gain no new author obligation"

§3 says the ordinary facet "is derived from the existing terminal/lifecycle
proof" and "creates no additional proof field for its author". That is true
here, and for a reason better than a convention: `Grass/Process/Run.lean`'s
`ProcessRunTransition.terminate` **cannot be formed** without a
`TerminalDemandClassification`, so every terminating transition already carries
its exact disposition. `terminal_transitions_have_exact_disposition` extracts it
by case analysis, and `TerminationFacet.ordinary` therefore takes no argument at
all.

An author of a straight-line helper writes `.ordinary` and owes nothing, which
is what the sentence promises. If the run relation ever let a process terminate
without a classification, that theorem would break here rather than quietly
weakening the facet — which is the point of deriving it rather than asserting
it.

## "The bridge cannot discard it after manufacturing a liveness contract"

§3 again: "The cooperative and supervised facet constructors retain the complete
`CancellationBackedContract`, including the exact summary witness. Runtime and
proof-level cancellation transitions consume that retained summary to identify
the affine request occurrence, safe state, delay premise and disposition; the
bridge cannot discard it after manufacturing a liveness contract."

`retainedContract` is that: total over the facet, returning the contract for the
two constructors that have one. `cooperative_retains_its_contract` says the
contract you get back is the one that went in — by `rfl`, because the
constructor holds it rather than summarising it. A facet that stored a derived
liveness fact and dropped the contract would be the failure the sentence warns
about, and could not typecheck against this definition.

## What is parameterised, and why

`SupervisorPolicy` and the version family are types `docs/PROCESS.md` names and
does not declare, and supervision is not `Grass.Process`'s to invent — §3 puts
`oneForOne`, `oneForAll` and `restForOne` among the weave combinators. They are
parameters here, the same way `Grass/Process/Network/World.lean` parameterises
the obligation ledger: a plan supplies them, and this layer states the facet
without claiming to own them.

`TerminationPremiseFamily`, which §3's `cooperative` demand also carries, is
deferred with the liveness half in `Grass/Process/Termination.lean` — see
`ReachesSafePointObligation` there. The demand below indexes on the cause type
alone, which is what a consumer needs to know *which* causes a facet covers.

One tightening this module makes over §3's declaration: the retained contract is
against `accept.terminalRemainder`, the *specification's* remainder law, rather
than any law the author cares to name. §3 writes `ProcessTerminationContract p`
with the law left open, which would let a facet promise cancellation whose
dispositions the specification does not accept. Tying it to the acceptance is
free — a `ProcessCorrect` already carries one — and it is what makes
`retained_contract_forbids_arbitrary_death` a fact about *this* process rather
than about some other law's contract.
-/

namespace Grass.Process

universe u w

/-! ## Every terminating transition already disposes of what it held -/

variable {p : ProcessSpec.{u, w}}

/--
A run's terminating transitions all carry an exact demand disposition.

§3's `TerminalTransitionsHaveExactDisposition`, and it holds of every process
rather than being a field an author supplies — see the module note.
-/
def TerminalTransitionsHaveExactDisposition
    (law : TerminalRemainderLaw p) (request : p.Request) : Prop :=
  ∀ {state : p.State} {outstanding : Bag p.Demand}
    {observations : Trace p.Observation} {result : p.TerminalResult},
    ProcessRunTransition law request
      (.running state outstanding observations)
      (.terminal state result observations) →
    Nonempty (TerminalDemandClassification law request state result outstanding)

/--
**And it is a theorem, not an obligation.**

`ProcessRunTransition.terminate` is the only constructor whose target is a
terminal state, and it cannot be formed without the classification. So the
disposition is already there for every process, and
`TerminationFacet.ordinary` below can take no argument.

This is where §3's "pure serial functions gain no new author obligation" is
kept. If the run relation ever admitted a terminating transition without a
classification, this proof would fail here — which is why the facet derives it
rather than asking for it.
-/
theorem terminal_transitions_have_exact_disposition
    (law : TerminalRemainderLaw p) (request : p.Request) :
    TerminalTransitionsHaveExactDisposition law request := by
  intro state outstanding observations result transition
  cases transition with
  | terminate isTerminal classification => exact ⟨classification⟩

/-! ## What a process promises about stopping -/

/--
The termination promise a process exports.

`docs/PROCESS.md` §3's `TerminationDemand`. `Policy` and `Versions` are
parameters; see the module note.
-/
inductive TerminationDemand (Policy : Type) (Versions : Type) : Type 1
  /-- No promise beyond finishing or faulting. -/
  | ordinary
  /-- Cancellable for these causes. -/
  | cooperative (Cause : Type)
  /-- Under this supervisor. -/
  | supervised (policy : Policy)
  /-- Upgradable across these versions. -/
  | versioned (versions : Versions)

/--
The facet a process attaches to keep that promise.

Indexed by the demand, so a consumer holding a `TerminationFacet correct
(.cooperative Cause)` knows both that the process is cancellable and which
causes it covers.
-/
inductive TerminationFacet {accept : ProcessAcceptance p}
    (correct : ProcessCorrect p accept) (request : p.Request)
    (Policy : Type) (Versions : Type) :
    TerminationDemand Policy Versions → Type (max 2 (u + 1) (w + 1))
  /--
  The ordinary facet. **No argument.**

  §3: "the ordinary facet is derived from the existing terminal/lifecycle
  proof… Pure serial functions, straight-line helpers, and uncancellable leaf
  processes gain no new author obligation."
  `terminal_transitions_have_exact_disposition` is what makes that true rather
  than merely stated.
  -/
  | ordinary : TerminationFacet correct request Policy Versions .ordinary
  /--
  Cooperative cancellation, retaining the whole contract.

  Not a derived liveness fact: the contract itself, so a later transition can
  recover the safe points, the permitted modes and the disposition from it.
  -/
  | cooperative (contract : ProcessTerminationContract accept.terminalRemainder request) :
      TerminationFacet correct request Policy Versions (.cooperative contract.Cause)
  /-- Supervised, retaining the contract and naming the policy. -/
  | supervised (contract : ProcessTerminationContract accept.terminalRemainder request)
      (policy : Policy) :
      TerminationFacet correct request Policy Versions (.supervised policy)
  /-- Upgradable. The handoff is the version family's, not this layer's. -/
  | versioned (versions : Versions) :
      TerminationFacet correct request Policy Versions (.versioned versions)

namespace TerminationFacet

variable {request : p.Request} {accept : ProcessAcceptance p}
  {correct : ProcessCorrect p accept} {Policy Versions : Type}

/--
The contract a facet retains, if it has one.

§3: "the bridge cannot discard it after manufacturing a liveness contract."
Total over the facet, so there is no constructor whose retained contract is
undefined — and the two that promise cancellation both have one.
-/
def retainedContract {demand : TerminationDemand Policy Versions} :
    TerminationFacet correct request Policy Versions demand →
    Option (ProcessTerminationContract accept.terminalRemainder request)
  | .ordinary => none
  | .cooperative contract => some contract
  | .supervised contract _ => some contract
  | .versioned _ => none

/--
**A cooperative facet gives back exactly the contract it was built from.**

By `rfl`, because the constructor holds the contract rather than summarising it.
That is the whole of §3's sentence: a facet that stored a derived liveness fact
and dropped the contract could not be written against this definition.
-/
@[simp] theorem cooperative_retains_its_contract
    (contract : ProcessTerminationContract accept.terminalRemainder request) :
    (TerminationFacet.cooperative (correct := correct) (request := request)
      (Policy := Policy) (Versions := Versions) contract).retainedContract
      = some contract := rfl

/-- And so does a supervised one, which is where a supervisor reads it from. -/
@[simp] theorem supervised_retains_its_contract
    (contract : ProcessTerminationContract accept.terminalRemainder request)
    (policy : Policy) :
    (TerminationFacet.supervised (correct := correct) (request := request)
      (Versions := Versions) contract policy).retainedContract = some contract := rfl

/--
An ordinary facet retains nothing, and that is correct rather than a loss.

§3: the weakest summary's "`exportedContract` is `none`". A process that
promises only to finish or fault has no cancellation contract to retain, and
inventing one for it would be the additional author obligation §3 says it does
not have.
-/
@[simp] theorem ordinary_retains_nothing :
    (TerminationFacet.ordinary (correct := correct) (request := request)
      (Policy := Policy) (Versions := Versions)).retainedContract = none := rfl

/--
**Every promise of cancellation comes with the contract that backs it.**

The general form: if a facet's demand is `cooperative` or `supervised`, it
retains a contract. There is no way to claim cancellability without carrying the
thing that justifies it.
-/
theorem cancellable_facets_retain_a_contract
    {demand : TerminationDemand Policy Versions}
    (facet : TerminationFacet correct request Policy Versions demand)
    (promises : (∃ Cause, demand = .cooperative Cause) ∨
      ∃ policy, demand = .supervised policy) :
    ∃ contract, facet.retainedContract = some contract := by
  cases facet with
  | ordinary =>
    rcases promises with ⟨_, absurdDemand⟩ | ⟨_, absurdDemand⟩ <;>
      exact absurd absurdDemand (by simp)
  | cooperative contract => exact ⟨contract, rfl⟩
  | supervised contract _ => exact ⟨contract, rfl⟩
  | versioned _ =>
    rcases promises with ⟨_, absurdDemand⟩ | ⟨_, absurdDemand⟩ <;>
      exact absurd absurdDemand (by simp)

/--
**A facet that promises cancellation yields a contract that forbids arbitrary
death.**

The point of retaining the contract rather than a summary of it: a supervisor
holding a cooperative or supervised facet can *derive* that it cannot
manufacture a safe forced stop, instead of being told so.

An earlier revision stated this with the contract supplied and the facet only
mentioned in a hypothesis it never used — which made it a theorem about
contracts wearing a facet's name. Here the facet is the source of the contract,
so the statement is about what holding a facet buys you.
-/
theorem cancellable_facet_forbids_arbitrary_death
    {demand : TerminationDemand Policy Versions}
    (facet : TerminationFacet correct request Policy Versions demand)
    (promises : (∃ Cause, demand = .cooperative Cause) ∨
      ∃ policy, demand = .supervised policy) :
    ∃ contract : ProcessTerminationContract accept.terminalRemainder request,
      facet.retainedContract = some contract ∧
        ∀ (mode : TerminationMode) (cause : contract.Cause) (state : p.State)
          (outstanding : Bag p.Demand),
          ¬ contract.SafePoint state →
          contract.permitted mode cause state outstanding → mode = .faulted := by
  obtain ⟨contract, retained⟩ := facet.cancellable_facets_retain_a_contract promises
  exact ⟨contract, retained, fun _ _ _ _ notSafe allowed =>
    contract.only_a_fault_happens_off_a_safe_point notSafe allowed⟩

end TerminationFacet

end Grass.Process
