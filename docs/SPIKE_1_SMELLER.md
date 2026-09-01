# Total-system adversarial review — round 15

Verdict: **not at fixpoint**.

Round 15 closes the eleven defects reported in Round 14 at the displayed
process-interface level. Initial and terminal runs, dependent child binding,
historical nominal allocation, byte lifecycle/conservation, chunk extensionality,
resource valuation, affine channel credit, scope partitioning, component model
bindings, closed standard-realizer lookup, and collision-independent cache replay
now all have substantially better types.

That repair exposed the next layer. The canonical sequential adapter cannot
construct the initial effects its own proof sketch uses. The serial-call escape
hatch lacks the exhaustive exit and atomicity evidence needed to remain a
conservative process realization. The scope theorem subtracts resources without
an algebra supporting subtraction. The spike source corpus is not the complete
source described by the annotated spikes, and several cross-layer proof
junctions are absent. Spike 5 also contains concrete clock, Vulkan-feature,
lifetime, SPIR-V-interface, and artifact-consumption failures.

Two independent fresh-context passes reviewed proof feasibility/process
semantics and the five spike fixtures. Their results were rechecked and
integrated with a root total-system review; no axis finding is treated as a
standalone judgment.

## Round 14 closure audit

| Round 14 finding | Status in round 15 | Evidence or qualification |
| --- | --- | --- |
| 1. Process start/termination unsound | **Closed.** | `Initial` emits state/demands/observations, `Terminal` is request indexed, the unique run-initial forms are displayed, and only running states step (`PROCESS.md:60-68`, `PROCESS.md:163-232`). |
| 2. Parent demand can start unrelated child | **Closed structurally.** | `ChildDemandBinding` connects exact parent occurrence, child initial run, exhaustive outcomes, choices, resources, obligations and cancellation; spawn/routing/lowering consume it (`PROCESS.md:821-878`). |
| 3. Freshness is ambient | **Closed.** | Allocation is a before/after transition law: allocated nominals are disjoint from prior history, the after-history is exact union, and nonallocation preserves it (`PROCESS.md:762-783`). |
| 4. Byte lifecycles are enums and lose partial effects | **Closed structurally.** | Phase-indexed ingress/egress states, legal constructors, exact prefix/residual dispositions, conservation, token consumption and no-step-after-terminal theorems are present (`PROCESS.md:447-683`). |
| 5. Chunking theorems are under-premised | **Closed.** | Capacity splitting, mapped cuts/outcomes and `ChunkExtensional` parser premises replace the earlier unconditional bisimulation claim (`PROCESS.md:688-716`). |
| 6. Resource valuation lacks laws | **Closed.** | Empty, monotonicity, disjoint union, attribution and affine-transfer laws are fields of `ResourceMetric` (`PROCESS.md:1404-1422`). Finding 3 below concerns a new unsupported subtraction outside those laws. |
| 7. Capacity credit is prose | **Closed structurally.** | Product credit, a fixed total partition, exact transition laws, insufficient-credit uninhabitedness and the backpressure frontier are displayed (`PROCESS.md:1432-1475`, `PROCESS.md:1538-1544`). |
| 8. Subtree bound is opaque | **Closed structurally.** | Scope partition, explicit formula inputs, temporal flux, shared attribution, termination custody and nested composition are displayed (`PROCESS.md:1498-1536`). Finding 3 below shows the proposed formula is not yet derivable from the chosen algebra. |
| 9. Component models claim whole-program correctness | **Closed in the architecture; not closed in fixtures.** | `ImplementationBinding` is source-scope/component-requirement indexed and whole-application behavior composes outside it (`REFINEMENT.md:124-162`; `VERIFIED_PROGRAM.md:100-108`). Findings 5 and 6 show the spike files omit required bindings. |
| 10. Standard realizer uses ambient typeclass search | **Closed.** | A named closed registry has exact lookup and uniqueness evidence; platform choice remains explicit (`PROCESS.md:1030-1067`). |
| 11. Merkle roots risk becoming logical evidence | **Partially closed.** | Replay now requires actual canonical source/boundary/import/theorem/policy equalities and explicitly says hashes prove none (`REFINEMENT.md:324-372`). Finding 9 addresses contradictory later scalability prose and the missing cost model for constructing those equalities. |

## Ranked round 15 findings and exact repairs

### 1. [P0] The canonical sequential adapter consumes effects its input cannot express

`DirectRelationalProgram.initial` produces only a predicate on a state, and
`Step` produces a new state and observations. Neither returns issued effects,
effect occurrences, or a pending-effect bag (`PROOF_FEASIBILITY.md:37-42`). Yet
the construction immediately adds a live-child map, claims that it erases to
`direct.pending effects`, creates “initial children named by the direct initial
effect inventory,” and handles an effect-issue case (`PROOF_FEASIBILITY.md:66-95`).
No displayed field supplies any of those values or equations.

`effectSites : FiniteEffectSiteInventory Step` cannot repair this. An inventory
of possible sites is not the dynamic multiset issued by a particular initial
state or transition, and it cannot establish exact occurrence multiplicity.
Thus `SequentialAdapter` is currently a claimed synthesis step over missing
semantic data—the failure the document says it rejects.

**Exact repair:** make initial and transition outputs structured and exact, for
example:

```lean
Initial : Request -> State -> Multiset (EffectDemand boundary) ->
          List boundary.Observation -> Prop
Step : State -> DirectEvent boundary -> State ->
       Multiset (EffectDemand boundary) ->
       List boundary.Observation -> Prop
Pending : State -> AbstractDemandBag (EffectDemand boundary)
```

Supply issuance/consumption equations tying each event and output multiset to
`Pending before/after`, plus a dependent site-to-child binding. The adapter may
generate identities, escrow and topology from those proofs; it may not discover
which effects exist. Add zero-effect, duplicate-equal-effect, initially pending,
issue-and-cancel, and effect-result-plus-new-effect fixtures.

### 2. [P0] The comment-free spike corpus is not the complete authored source it claims to be

`Spikes/README.md:3-17` calls the `.lean` files the expected author-owned source
and identifies each `Assembly.lean` as first-class authored assembly. The files
do not contain all bytes and expansions needed by their own references:

- the web-server source references `listen_socket`, `bind_address`, `wsa_data`,
  `worker_slots`, `route_body` and other objects, but closes `asm_source` without
  the annotated static-data block (`Spikes/4_Web_Server/Assembly.lean:39-42`,
  `:63`, `:382`, `:453`; compare `SPIKE_4.md:1079-1091`);
- gzip references `lengthBase`, `lengthExtra`, `distanceBase` and
  `distanceExtra` but contains no declarations for the complete codec tables
  (`Spikes/3_Gzip/Assembly.lean:352-404`); and
- the cube contains source-specific pseudobodies such as
  `enumerate_and_select_literal_loop`, destruction/selection/extent helpers and
  English `if`/`for each` cleanup, then closes with no static strings, Vulkan
  name tables, constants, ownership storage or macro definitions
  (`Spikes/5_Spinning_Cube/Assembly.lean:254`, `:316-343`, `:525-551`).

The annotated cube explicitly requires all macro instantiations to be inlined in
a line-auditable raw listing before implementation review
  (`SPIKE_5.md:1304-1307`). A prose expansion elsewhere is useful design material,
but it does not make the expected `.lean` source complete or give
`SourceElaboratesExactlyTo` an exact expansion value.

**Exact repair:** put every spike-specific macro definition, static object,
table and expansion input into the imported source closure, and generate a
checked macro-expanded raw listing from that closure. The comment-free fixture
and annotated listing must be two renderings of the same source value. Reject
undefined tokens, undeclared static symbols, hidden helper bodies and a listing
whose expansion identity is not an input to `VerifiedProgram`.

### 3. [P0] The scope-bound proof uses subtraction absent from its resource algebra

The feasibility sketch assumes only an ordered commutative resource algebra:
empty, combination, order, monotonic valuation and affine transfer
(`PROOF_FEASIBILITY.md:292-301`; `PROCESS.md:1404-1422`). It then defines:

```text
scopeBudget = ... ⊕ maximumAdmittedInbound ⊖ creditedOutbound
```

(`PROOF_FEASIBILITY.md:303-312`). No residual/subtraction operation, existence
condition, cancellation law, truncation convention, or order theorem is present.
This is false for many useful ordered commutative monoids and is especially
ambiguous for products whose coordinates use sum, max, shared-once and transfer
rules.

**Exact repair:** state the theorem without subtraction, e.g.
`scopeUse ⊕ creditedOutbound ≤ grossBudget`, and derive a smaller numeric bound
only for axes carrying a proved cancellative/residuated structure and the side
condition that the credit is available. Otherwise keep outbound transfer as an
explicit relational term. Add max, natural-number, shared-attribution and
noncancellative product fixtures.

### 4. [P0] Spike 5's host does not meet its clock and Vulkan contracts

There are several independent falsifiers in the expected source:

1. The source checks `QueryPerformanceFrequency`'s call result and executes
   `cmp [qpcFrequency],0` but has no branch. Zero or negative frequency reaches
   division (`Spikes/5_Spinning_Cube/Assembly.lean:171-177`, `:448-450`). The
   annotated source does include `jle fail_init` (`SPIKE_5.md:730-733`), so the
   two supposedly authoritative sources disagree.
2. `CubeObservation.Accepts` requires strictly increasing frame times
   (`Spikes/5_Spinning_Cube/Spec.lean:31-37`), while the host rejects only a
   negative QPC delta and submits a frame for delta zero
   (`Spikes/5_Spinning_Cube/Assembly.lean:439-466`). A monotonic clock promises
   nondecrease, not a distinct tick per frame. The precious specification is
   unnecessarily strong here.
3. The host calls `vkCmdPipelineBarrier2` and `vkQueueSubmit2`, but device
   selection and creation enable only `dynamicRendering`; the Vulkan 1.3
   `synchronization2` feature is neither required nor enabled
   (`Spikes/5_Spinning_Cube/Assembly.lean:258-265`, `:429`, `:468`, `:480`).
4. `WM_CLOSE` destroys the window immediately while the Vulkan surface remains
   owned until later cleanup (`Spikes/5_Spinning_Cube/Assembly.lean:202-205`,
   `:538-540`), contradicting the spike's own window/surface dependency order.

**Exact repair:** restore the positive-frequency branch in the one authoritative
source; make the product spec require nondecreasing opportunity/sample times and
elapsed-time-consistent angles, or explicitly coalesce equal samples; rename
`presentedAt` to the instant actually sampled unless a display-time provider is
added; require/query/enable `synchronization2`; and defer HWND destruction until
dependent surface/device work is settled. The floating representation theorem
must also state its rounding/error relation to ideal elapsed rotation rather
than silently identify binary32 shader inputs with an exact abstract angle.

### 5. [P0] Sort and gzip do not close the advertised model-to-requirement chain

The architecture now has the right economic division: prove stable sorting and
codec mathematics against a Lean model once, then prove only that exact assembly
scope refines that model. The comment-free fixtures do not implement the chain
their annotated spikes promise.

`SPIKE_2.md:466-472` requires both `sortSource_refines_model` and
`stableSort_contract_connects`. `Spikes/2_Sort/Assembly.lean:402-409` instead
contains only a whole-driver `AssemblyImplements` theorem and an extracted serial
function. It supplies neither an `AssemblyRefinesImplementation` theorem with
the descriptor representation nor a component-contract-to-requirement theorem.

Gzip does contain `sourceRefinesModel`, but the fixture omits the required
`fixed32K_contract_connects` junction (`Spikes/3_Gzip/Assembly.lean:658-661`;
`SPIKE_3.md:114-127`). In both programs `Program.lean` invokes bare
`verify_assembly`, so the missing component binding is either magically inferred
or algorithm correctness is being re-proved in the whole-assembly path.

**Exact repair:** make the exact `ImplementationBinding` values first-class in
the fixture: source scope, representation, model certificate, assembly-to-model
refinement and component-to-program requirement connection. Pass the bundle to
`verify_assembly` or make a transparent constructor consume those exact named
proofs. Mutation tests must show a merge/codec body edit invalidates only its
assembly-to-model proof, while a model-contract change invalidates exactly the
component junction and consumers.

### 6. [P0] The cube's cross-ISA artifact connection is incomplete

The artifact fixture proves only that the serialized shader words occur at two
RVAs (`Spikes/5_Spinning_Cube/Artifact.lean:27-33`). The annotated design requires
the stronger cross-ISA junction: exact process plan and machine source, every
shader-create use consuming those exact ranges, and Vulkan execution consuming
the proved SPIR-V semantics (`SPIKE_5.md:1385-1440`). Merely embedding correct
words does not show that the host passes them to `vkCreateShaderModule`, retains
the resulting module identity in the selected pipeline, or connects device
execution to `vertexCorrect`/`fragmentCorrect`.

**Exact repair:** add the complete `CrossIsaArtifactConnection` to the
comment-free closure. Mutate an RVA, byte
length, `pCode`, shader-module handle, pipeline-stage module, entry-point name or
embedded word; the first affected exact adjacency must fail.

### 7. [P1] A serial call is still an under-specified atomicity escape hatch

`SerialFunctionContract` has useful names for pre/post, footprint, obligations,
resources, faults, termination and no-frontier (`PROCESS.md:113-134`), but the
call theorem does not display exhaustive normal/fault/partial exit mapping or the
simulation which turns many machine steps into one logical step. A footprint
alone does not authorize hiding observable intermediate writes to shared state.
`WellFoundedInternalExecution` also hides the actual rank and recursive-SCC
composition rule.

The feasibility section uniquely omits the document's promised automation
boundary, falsification fixture and real fallback (`PROOF_FEASIBILITY.md:121-148`).
Calling this “ordinary Hoare composition” does not settle concurrent atomicity,
partial mutation on fault, resource custody on every exit, or bounded internal
stuttering.

**Exact repair:** require exhaustive call exits; exact resource/obligation state
for every exit; a displayed rank including recursive SCC edges; exclusive
ownership or a supplied linearization/noninterference proof for shared state;
and a finite-stuttering simulation from each machine call trace to the one
process transition. If responsiveness needs more than termination, require a
work bound. Falsify hidden provider entropy, unranked recursion, intermediate
shared writes, a fault after partial mutation and custody transfer. The honest
fallback is explicit process steps or a child frontier.

### 8. [P1] The feasibility sketches are not exhaustive where they claim induction or coinduction

The worker-pool sketch says preservation is one case per `NetworkTransition`
but lists only accept, byte issue/resolution, timeout, close, worker death and
shutdown (`PROOF_FEASIBILITY.md:176-206`). The actual family includes process
step, spawn, send, receive, commit, child lifecycle, process termination,
channel close, sender/receiver/channel death, drop, reroute, coalesce, join,
detach and restart (`PROCESS.md:735-741`). Each constructor needs a preservation
case or an explicit unreachability premise; otherwise `weaveCorrect` is a name
for the missing proof.

The serialization sketch similarly says the graph-to-serial proof repeatedly
selects graph transitions (`PROOF_FEASIBILITY.md:347-362`), while complete
graph-to-serial coverage is itself a field being claimed
(`PROCESS.md:1196-1207`). It does not give the local scheduler-coverage lemma,
productive infinite extension, or the finite/infinite/divergent/pending/maximal
case split.

**Exact repair:** publish constructor-indexed proof tables for the server
invariant, including preserve-or-unreachable evidence for every transition.
For serialization, require local enabled-transition coverage and show the
finite induction and productive coinduction explicitly. Add starvation, finite
stuttering, infinite internal execution, pending child, fault and maximal
terminal fixtures.

### 9. [P1] Collision-independent replay and the claimed sublinear edit path are not yet reconciled

The replay surface correctly says Merkle hashes only locate a candidate and that
actual source, boundary, imports, theorem type and policy equality must be
kernel-checked (`REFINEMENT.md:324-372`). Later it says unchanged sibling roots
*prove* negative reuse and forbids flat manifest reconstruction on a leaf edit
(`REFINEMENT.md:397-406`). The feasibility sketch does not construct those
actual equalities sublinearly (`PROOF_FEASIBILITY.md:518-547`).

If roots prove nothing, some trusted or checked mechanism must identify the
current canonical values to which the imported theorem is transported. Reading
and hashing source bytes may be unavoidable even when proof elaboration is
reused. Conflating source discovery with theorem rechecking makes the economics
unfalsifiable and risks quietly promoting the build database or root equality
into logical evidence.

**Exact repair:** state that roots locate cached subtree replay certificates;
the imported certificate and current consumer interface establish applicability
through actual kernel-visible values. Separately specify and measure source
discovery/hashing, module import, equality construction, elaboration, kernel
checking, composition and final serialization. If a persistent change oracle is
trusted for skipping source reads, put it in the operational trust/performance
ledger, never the logical theorem.

### 10. [P1] The gzip fallback may not hide bytes already committed externally

The gzip sketch correctly banks construction correctness in a small streaming
model and reserves assembly proofs for representation/control refinement
(`PROOF_FEASIBILITY.md:384-411`). Its fallback says to narrow the public failure
observation to the largest committed syntactic prefix
(`PROOF_FEASIBILITY.md:425-430`). That is invalid if a provider has already
committed a longer arbitrary byte prefix: observation filtering cannot make a
physical stdout effect disappear.

**Exact repair:** retain the exact committed bytes in the specification and
prove that they are extendable to a valid member/construction state, or buffer
transactionally until a complete public unit can be committed. A narrower
logical observation is acceptable only if the platform contract separately
states and preserves the full physical byte effect.

### 11. [P1] The million-to-tens-of-millions scale target has no falsifiable gate

`VISION.md:5-10` names millions of assembly lines, but its acceptance gates use
only “repository scale” and measurements (`VISION.md:269-299`). Hierarchical
reuse likewise asks for “several shard sizes” and “representative repository
sizes” without a minimum fixture or count-based threshold
(`PROOF_FEASIBILITY.md:539-552`; `REFINEMENT.md:397-413`). A 20,000-line fixture
could satisfy that prose while saying nothing about the target.

**Exact repair:** require generated but semantically heterogeneous 1M and 10M+
instruction/source fixtures, plus at least one composed long-running system.
Publish count-based limits for declarations elaborated, certificates
kernel-checked, replay/composition nodes visited, peak live proof state and edit
impact cones. Report unavoidable bytes scanned and artifact bytes regenerated
separately. Wall time remains environment-sensitive evidence, not the theorem;
the structural counters are the acceptance contract.

## Specification and product judgment

The revised vision is directionally correct. Games, databases, operating
systems and other long-lived systems are the objective; the five spikes are
explicitly narrow architecture fixtures rather than claims of product coverage.
The one-process-algebra decision is defensible only if direct serial calls remain
a proved local refinement and do not acquire hidden entropy, interleaving,
lifecycle or custody semantics. Finding 7 is therefore architectural, not a
request to turn every function into an actor.

The sort and gzip split is also the right one: data-manipulation correctness
belongs to the Lean implementation model, while literal assembly proves exact
representation/control refinement to it. The current documents state that
policy, but the expected sources do not yet instantiate it completely.

For the cube, strict timestamp increase is not a product requirement and should
not be precious. Nondecreasing monotonic samples plus an elapsed-time rotation
law are both more believable and less implementation-constraining. Conversely,
the exact host/shader consumption chain, feature enablement, dependency-safe
cleanup and numerical refinement are correctness requirements and cannot be
weakened to ease proofs.

## Proof-economy and authorship judgment

The desired author surface remains plausible: precious spec, explicit platform
plan, assembly, and a closing command for standard cases; explicit process plans
and interference witnesses only where topology is genuinely product- or
implementation-relevant. The corpus now distinguishes reviewed replaceable
construction from precious semantics much better than Round 14.

The current feasibility document nevertheless violates its own six-part rule.
Only the canonical-adapter section explicitly provides claim, caller input,
construction, bounded automation, falsification fixture and fallback. Most later
sections imply some of these in prose; the serial-call section omits the critical
ones entirely. At large scale, theorem names such as `WellFoundedInternalExecution`,
`FiniteEffectSiteInventory`, `TemporalInsideOutsideAndBoundaryFluxConservation`
and `ActualImportedDeclarationEnvironmentEquality` are acceptable interface
placeholders only when their constructors and residual author obligations are
made finite and measurable.

Do not expand every application proof to mirror these internals. Put exact
occurrence bookkeeping, ordinary resource sums, ABI mechanics, macro expansion,
cache replay and standard effect bindings behind transparent library
constructors. Keep ranks, ownership/interference choices, component contracts,
product-visible failure policy and nonstandard lifecycle semantics authored.
That is the line which can plausibly survive ten million instructions and
specification change.

## Fixpoint decision

**No fixpoint.** Round 14's eleven findings are largely repaired, but Round 15
contains six P0 closure/correctness failures and five P1 feasibility/economics
failures. The next review must re-audit every item above against the actual
comment-free fixtures, not only amended prose. No library or spike implementation
was built or accepted in this review.

---

# Total-system adversarial review — round 16

Verdict: **not at fixpoint**.

Round 16 reread the current corpus and every current comment-free spike fixture.
The concrete Round 15 repairs are substantial: the direct sequential program now
emits exact dynamic effect bags; resource subtraction is replaced by a gross
inequality plus optional lawful residuation; serial calls have exit-indexed
fault/custody, rank, visibility and finite-stuttering evidence; process weaving
and serialization now name constructor-indexed coverage; sort and gzip carry
explicit model bindings; the cube clock, Vulkan feature, lifetime, numerical and
cross-ISA artifact junctions are repaired; exact source closures now include the
previously missing data/macros; gzip retains physically committed failure bytes;
and the 1M/10M scale gate is numeric.

The newly integrated resource/spec-process/staged-refinement architecture is not
yet constructible from its displayed declarations. The main failures are exact
dependent-index and layer-connection failures, not a request for more prose.
Two fresh-context axis reviews were integrated with a root corpus/fixture review.

## Round 15 closure audit

| Round 15 finding | Round 16 status | Current evidence |
| --- | --- | --- |
| 1. Sequential adapter cannot express effects | **Closed.** | `DirectRelationalProgram` now has exact initial/step outputs, `Pending`, issuance/consumption equations, dependent bindings and mutation fixtures (`PROCESS.md:1121-1169`). |
| 2. Spike source corpus is incomplete | **Partially closed.** | Sort, gzip and server now have data/macro/source-closure modules; cube has an explicit source closure. Cube closure proofs use forbidden `native_decide`, so the verified closure is still unacceptable; finding 7 below. |
| 3. Scope theorem uses unsupported subtraction | **Closed.** | The generic theorem uses `scopeUse ⊕ creditedOutbound ≤ grossBudget`; a smaller bound requires a `ResiduatedResourceAxis` and availability proof (`PROCESS.md:1666-1714`; `PROOF_FEASIBILITY.md:403-441`). |
| 4. Cube clock/Vulkan/lifetime contract failures | **Closed in the fixture.** | Positive QPC frequency is checked, nondecreasing samples and absolute epoch rotation are modeled, `synchronization2` is checked/enabled, and surface destruction precedes HWND destruction (`Spikes/5_Spinning_Cube/Assembly.lean:175-184`, `:267-270`, `:446-465`, `:531-547`; `Spec.lean:35-42`; `Model.lean:26-37`). |
| 5. Sort/gzip model-to-requirement chain absent | **Closed.** | Both `Bindings.lean` files name source scope, representation, assembly/model refinement, contract connection and `ImplementationBinding`, and their programs consume those bindings. |
| 6. Cube cross-ISA artifact connection absent | **Closed structurally.** | The fixture now connects exact plan/source, shader ranges, create uses, pipeline stages and provider SPIR-V semantics (`Spikes/5_Spinning_Cube/Artifact.lean:35-61`). |
| 7. Serial call is an atomicity escape hatch | **Closed structurally.** | Exhaustive exit states, partial faults, custody, SCC rank, visibility/linearization, finite stuttering, bounded automation, falsifiers and honest fallbacks are displayed (`PROCESS.md:139-237`; `PROOF_FEASIBILITY.md:141-224`). |
| 8. Weaving/serialization sketches are non-exhaustive | **Closed structurally.** | The actual transition constructors have a case table and serialization exposes enabled-transition coverage, guarded extension and infinite/maximal cases (`PROOF_FEASIBILITY.md:268-322`, `:487-571`). |
| 9. Exact replay conflicts with sublinear reuse | **Closed as an acceptance contract.** | Source discovery is separated from semantic replay, hashes remain locators, and leaf reuse reports source-byte work separately from zero sibling elaboration/kernel checks (`PROOF_FEASIBILITY.md:715-765`; `REFINEMENT.md:521-537`). |
| 10. Gzip fallback hides committed bytes | **Closed.** | Exact committed bytes remain visible and must be extendable to a valid member or transactionally buffered (`PROOF_FEASIBILITY.md:616-627`). |
| 11. 1M–10M scale target is unfalsifiable | **Closed as a stated gate.** | Mandatory 1M and 10M+ heterogeneous fixtures and structural work counters are specified (`VISION.md:386-403`; `PROOF_FEASIBILITY.md:755-765`). Implementation evidence remains future work. |

## Ranked round 16 findings

### 1. [P0] The explicit resource value does not pin its behavior-defining capability dictionary

`Specification resources` retains the inferred `ResourceModel R` argument, but
the spec-specific capability classes used to construct it are absent from the
resulting index. `HasResourceLimit` supplies `limit`, `exhaustion` and `lifecycle`,
and `WebServerResources` additionally supplies connection capacity and deadlines
(`SEMANTICS.md:135-170`). Those are semantic data, not merely laws. Nevertheless
`webServerSpec` takes `[WebServerResources R]` and returns only
`Specification resources` (`Spikes/4_Web_Server/Spec.lean:42-57`).

**Failure fixture:** choose `R := Unit`, one `ResourceModel Unit`, and two lawful
`WebServerResources Unit` dictionaries—one permitting one connection with a
short deadline, another one hundred with a long deadline. Both applications
have type `Specification ()`. A downstream theorem can infer a third ambient
dictionary rather than recover the dictionary which created the body.

**Required closure:** bundle every semantically material capability projection
into the explicit resource-semantics value/index, or prove the capability
dictionaries canonical/subsingleton and reject competing instances. Downstream
proofs must project the selected limits, exhaustion, lifecycle and deadlines
from `spec`; they must never rerun open-ended typeclass selection. Typeclasses may
expose laws for those exact operations, not silently select alternative semantic
operations.

### 2. [P0] The staged graph interface does not type against `Specification`

`Specification` has only `body` and `requirements`; its body may be relational,
or its process constructor may contain one
`AbstractSpecificationProcessNetwork` (`SEMANTICS.md:159-170`). The staged API
instead quantifies over undefined `SpecProcess resources` and projects
`spec.processRoles` and `spec.protocol` from every specification
(`REFINEMENT.md:153-169`). No such type or projections are displayed.

**Failure fixture:** instantiate `BlendedProcessGraph` for
`SpecificationBody.relational contract`. There is no role family. Even an
`ofProcesses` specification cannot expose the claimed projections without a
dependent body equality and access through the contained network registry.

**Required closure:** define a resource-indexed spec-process type, then index the
staged API by an explicit
`network : AbstractSpecificationProcessNetwork resources` and evidence
`spec.body = .processes network`, or introduce a dependent
`ProcessShapedSpecification` subtype. Index nodes by the network's actual
registry/protocol schema. Relational specifications require a proved
normalization to the universal process algebra, not fictional process fields.

### 3. [P0] `PartialProcessRealization.close` does not consume the partial realization it claims to close

The corpus defines `blend graph : PartialProcessRealization spec`, then declares:

```lean
def PartialProcessRealization.close
    (complete : EveryNodeRealized graph)
    (coherent : AccumulatedProvidersResourcesAndObligationsCoherent graph) :
    ProcessRealization spec
```

(`REFINEMENT.md:172-178`). There is no
`partial : PartialProcessRealization ...` argument and no equality connecting the
free `graph` to the value returned by `blend`.

**Failure fixture:** construct completion/coherence evidence for graph B, then
invoke the displayed closer while the intended partial work was `blend A`.
Nothing in the signature consumes A or proves A = B.

**Required closure:** make the exact graph a dependent index retained by
`PartialProcessRealization`, and define
`close (partial : PartialProcessRealization spec graph) ...`. The returned
certificate must record that exact origin and accumulated requirement set so a
lookalike graph cannot donate closure evidence.

### 4. [P0] Top-level realization does not prove every reachable frontier is closed

`BlendedNode.realized` accepts a `SubsystemRealization` whose implementation is
itself a `BlendedSubgraph`, but that certificate has no recursive completeness
field (`REFINEMENT.md:156-170`). `EveryNodeRealized graph` can therefore inspect
only the outer labels. The claimed finite traversal also conflicts with role
families such as `ServerRole.connection (id : ConnectionId)`
(`Spikes/4_Web_Server/Spec.lean:15-19`), whose runtime instance space is not a
finite list.

**Failure fixture:** mark the connection role realized with a subgraph containing
one abstract storage child. Every outer node is `.realized`, yet an execution
still reaches an unresolved frontier. Alternatively require traversal of every
possible `ConnectionId`; closure is no longer finite.

**Required closure:** distinguish finite static role schemas from dynamic
instances. A parametric certificate may close every instance of one schema, but
completeness must recurse through every reachable child/adapter/provider
frontier within each realized subgraph. `close` rejects any unresolved descendant
without enumerating runtime identities.

### 5. [P0] Staged machine artifacts are introduced before platform selection and lost before the final gate

`SubsystemRealization` carries `LocalMachineArtifactFamily implementation`
inside Act 2 (`REFINEMENT.md:156-162`), before a `TargetProjection`,
`PlatformPlan`, provider environment, ABI or ISA is selected. Its closer returns
only `ProcessRealization spec` (`REFINEMENT.md:175-185`). The later
`MachineCertificate` independently selects `MachineSource` and contains no
equality/coverage edge back to those local artifacts
(`VERIFIED_PROGRAM.md:90-123`). Section 12 nevertheless says realized nodes
contribute artifacts and that closure checks platform/API/ABI/ISA coherence
(`PROOF_FEASIBILITY.md:777-845`).

The displayed coherence premise names only providers, resources and obligations;
it is not indexed by a target projection/plan, ABI, ISA, local artifact family or
exact discharge of `graph.requirements`.

**Failure fixture:** close a graphics subsystem using certified shader/source A,
then build the final machine tier from shader/source B with the same abstract
boundary. The staged artifact proof disappears. A second fixture combines
individually valid x86/SPIR-V nodes whose API versions/features are mutually
incompatible; the displayed closing premise has no target/ABI/ISA index with
which to reject it.

**Required closure:** either keep Act 2 purely portable and move artifact-bearing
refinement after explicit projection/plan selection, or return a dependent
`ClosedBlend` retaining the exact process realization, accumulated requirement
environment, target/provider/ABI/ISA evidence, scope-complete heterogeneous
machine sources/artifacts and cross-ISA connections. `MachineCertificate` must
consume that exact bundle. Do not prove a local artifact and then reconstruct an
unconnected twin later.

### 6. [P0] Spike 5's exact-source closure uses forbidden proof authority

`cubeSourceHasNoUnresolvedForms` and `cubeSourceManifestExact` are proved with
`native_decide` (`Spikes/5_Spinning_Cube/SourceClosure.lean:175-181`). They feed
`cubeVerified` through the exact source identity and host refinement
(`Program.lean:14-17`). The verified gate explicitly rejects native-evaluation
proof shortcuts (`VERIFIED_PROGRAM.md:448-453`; `FOUNDATION.md:24-27`).

**Failure fixture:** run the transitive proof-constant audit on `cubeVerified`;
both forbidden proofs are in its source-closure dependency cone.

**Required closure:** use a kernel-reducible proof (`rfl`, audited `decide`, or a
structural reflection theorem whose generated proof term is checked by the
kernel) within the exact allowlist. Make the transitive audit a required input to
the closing command. A finite manifest computation is not authorization for
`native_decide`.

### 7. [P1] Precious resource policy and concrete resource certificates have no exact junction

The precious layer gets named limits, exhaustion and lifecycle behavior from
`HasResourceLimit` (`SEMANTICS.md:138-157`). Process proofs independently choose
`ResourceMetric.Axis`, `Value`, valuation and budget
(`PROCESS.md:1565-1641`) and derive scope bounds (`PROCESS.md:1666-1714`). No
displayed certificate maps a specification axis from the exact `resources` value
to a concrete metric axis or proves that concrete exhaustion/allocation/release/
terminal transitions implement the selected policy. The shown
`ProcessPlanRealizes` has no resource-certificate field
(`PROCESS.md:1058-1068`), although spike fixtures invoke
`processPlanRealizes.resources.rootBound`.

**Failure fixture:** specify four connections, then use a lawful dummy
constant-zero metric and a budget of one hundred while the process admits forty.
The metric algebra can satisfy every displayed law without realizing the
precious limit or exhaustion behavior.

**Required closure:** add `ResourceAxisRealization spec resources plan metric
axis`, tying abstract `Value`, limit and policies to concrete holdings,
transition equations, exhaustion observations and terminal lifecycle. Make the
exact family mandatory in `ProcessPlanRealizes`/portable closure and define the
fixture projections from that field rather than an unstated `.resources`
extension.

### 8. [P1] Section 12's finite and infinite simulation cases are not constructive enough

The five transition cases in the section 12 sketch omit initialization and do
not exhaust the actual `NetworkTransition` family: cross-lens spawn, commit,
interrupt/environment violation, channel close/deaths, drop/reroute/coalesce,
join/detach/restart and population changes are not classified
(`PROOF_FEASIBILITY.md:804-830`; `PROCESS.md:830-855`). A spawned child whose
custody crosses the lens is neither purely replacement-local nor context-local.

The displayed `LocalProcessRefinement` hides behavior in
`replacement.Refines lens.source` and a generic progress field
(`REFINEMENT.md:131-139`). Forward finite-step matching plus progress preservation
does not construct productive infinite matching or rule out an implementation
which may stutter forever at an abstract pending frontier.

**Failure fixture:** refine one visible abstract step with an implementation
which may silently loop forever while retaining an enabled exit; every finite
prefix can stutter-match but a new maximal infinite behavior appears. Separately
spawn a selected child whose obligation is held by context and demand its
constructor case.

**Required closure:** expose the initial relation, exhaustive constructor-indexed
lens classifier, lifecycle/population cases, finite-stuttering rank, productive
infinite-extension/divergence reflection, frontier preservation and concrete-to-
abstract fairness projection. Every constructor receives preservation or exact
unreachability; the silent-loop mutation must fail locally.

### 9. [P1] The required staged-blending falsification fixture does not exist

Section 12 requires partial graphics/storage/simulation blends, both orders of
disjoint refinement, topology change, and rejection mutations
(`PROOF_FEASIBILITY.md:856-875`). No file under `Spikes/` uses `blend`,
`PartialProcessRealization`, `SubsystemRealization`, `BlendedProcessGraph` or
`refineSubgraph`. The cube directly constructs one explicit `ProcessPlan`; it
does not test abstract siblings or staged closure.

**Failure fixture:** the required fixture itself: graphics-only and storage-only
partial graphs must remain non-emittable; both disjoint orders must close to the
same projected behavior; one unresolved descendant, conflicting provider
feature, unframed shared invariant, changed occurrence multiplicity, increased
boundary flux and silent divergence must each fail a named local obligation.

**Required closure:** add a comment-free staged-refinement fixture—either a
dedicated architectural spike or a genuine staged variant of the cube/server—
which constructs partial values, demonstrates their rejection by
`VerifiedProgram`, and then supplies a complete coherent close. Do not count
section 12's desired test list as evidence that its interface is believable.

### 10. [P1] Several precious spec-processes author topology the product does not demand

Process-shaped precious syntax is legitimate when logical roles, independent
cancellation, custody or causality are product requirements. It is not a default
proof decomposition. The web spec makes `routeAuthority`, `admissionAuthority`,
`routeQuery`, request/response byte channels and close routing precious
(`Spikes/4_Web_Server/Spec.lean:15-40`). The product requires correct routing,
bounded admission, response/failure behavior and per-connection lifecycle; it
does not require a distinct route authority or query channel. Sort and gzip
likewise make input/algorithm/output pipeline roles precious
(`Spikes/2_Sort/Spec.lean:16-35`; `Spikes/3_Gzip/Spec.lean:12-31`) without showing
that role identity is observable.

**Failure fixture:** realize the web contract with an immutable route table local
to each connection and one admission counter, or realize sort/gzip as one serial
state machine. These implementations satisfy the desired external/resource
contract but must simulate invented precious internal traffic and cause spec
proof churn when decomposition changes.

**Required closure:** retain only product-significant role identity, custody and
causal constraints in precious process networks. Move route lookup ownership,
pipeline staging and internal byte routing into replaceable
`ProcessRealization` unless a named isolation, cancellation or observation law
requires them. For sort and gzip, prefer the relational/single-protocol precious
form and keep the algorithm model boundary separate from physical process
decomposition.

## Round 16 fixpoint decision

**No fixpoint.** Round 16 has six P0 closure/type/trust failures and four P1
semantic/economic validation failures. The resource-value direction and the
spec-process/physical-topology distinction are sound goals, but their current
dependent interfaces do not preserve the selected capability semantics or
connect staged values to the final machine/artifact gate. Section 12 is not yet
a constructive proof sketch for its advertised theorem family. No file other
than this review report was edited, and no undeveloped library was built.

# Total-system adversarial review — round 17

Commit reviewed: `420233e`.

This round reread the current governing interfaces and all five spike source
trees. Three fresh-context reviews independently attacked HTTP/2 cancellation,
resource/staged interfaces, and whole-spike shippability; this section is the
integrated review, including conflicts which become visible only across those
axes. The review did not treat a theorem-shaped identifier as evidence: the
`Grass.*` library is absent by stated scope (`Spikes/README.md:3-6`), so the
spikes can pressure-test an interface but cannot claim compiled proof closure or
hide a required instruction body in that future library.

The trust-source lint is clean: no spike proof contains `sorry`, `admit`,
`axiom`, unsafe proof promotion, or `native_decide`. Kernel `decide` remains
permitted. That does not cure false statements, missing source, or an
uncheckable dependency boundary.

## Round 16 closure audit

| Round 16 finding | Round 17 status |
|---|---|
| 1. Resource value did not pin its capability dictionary | **Still open.** A snapshot was added, but its selected axes are not tied to the captured dictionary; finding 8. |
| 2. Staged graph did not type against `Specification` | **Partially repaired.** Staging now requires a process-shaped witness, but `ProcessNormalization.shape` projects nonexistent fields and normalization reopens resource capture; finding 9. |
| 3. `close` did not consume its partial realization | **Locally repaired, globally open.** `close` now consumes `partial`, but returns a `ProcessRealization` whose origin cannot retain that graph; finding 10. |
| 4. Top-level closure was not recursive | **Stated, not demonstrated.** `internalFrontiersClosed` and schema-parametric closure are the right interface direction; the fixture premises are undeclared and uncompiled; finding 10. |
| 5. Machine artifacts were introduced early and then lost | **Architecturally improved, not connected.** Portable and machine blends are separated, but the closed portable graph provenance is erased before machine scope selection; finding 10. |
| 6. Cube source closure used `native_decide` | **Trust issue closed.** It now uses kernel `decide`; the asserted closure is nevertheless false for displayed symbols and uneconomical at target scale; findings 3 and 11. |
| 7. Precious resource policy had no concrete junction | **Partially repaired.** `ResourceAxisRealizationFamily` is mandatory, but axis identity remains underspecified and several spike root bounds are not exposed; finding 15. |
| 8. Section 12 omitted constructive infinite behavior | **Substantially repaired in prose.** It now names initialization, a total constructor classifier, silent rank, productive extension, divergence reflection, frontier preservation, and fairness projection (`PROOF_FEASIBILITY.md:811-907`). Required executable mutations remain absent; findings 10-11. |
| 9. No staged fixture existed | **File added, evidence absent.** `Staged.lean` is useful proposed caller syntax, but its single-use cube/engine witnesses are undeclared; finding 10. |
| 10. Precious specs overauthored topology | **Materially improved.** Sort and gzip are relational, and the remaining web/cube roles correspond to independently observable custody, ordering, or cancellation. Sort still makes an erased stability property precious; finding 16. |

## Findings

### 1. [P0] The corpus still does not contain the full assembly required to build Web or Cube

The corpus explicitly says its imported `Grass.*` libraries do not exist
(`Spikes/README.md:3-6`). Nevertheless, every Web macro is only a reference to an
absent library value (`Spikes/4_Web_Server/Macros.lean:6-121`). Those references
hide the frame parser, HPACK decoder, stream state machine, queues, flow-control
accounting, bounded ring, deadline logic, and writer selection invoked by
`Spikes/4_Web_Server/Assembly.lean:229-567`. Cube likewise registers absent
`AsmMacro.*` implementations (`Spikes/5_Spinning_Cube/SourceClosure.lean:145-162`)
for device enumeration, selection, allocation, swapchain retirement and reverse
cleanup. `serverSourceClosure.expand` and `cubeSourceClosure.expand` name future
computations; no raw expanded listing is present to review.

This is not merely missing proof infrastructure. It violates the spike rule
that the complete assembly to build the program is present and prevents review
of whether the invented standard-library semantics are implementable at a sane
proof cost.

**Failure fixture:** remove the future library import and attempt to enumerate
the raw instruction, data, frame, import and relocation manifests. Web loses
most of its program and Cube cannot expand its policy-bearing pseudo-operations.

**Required closure:** check in the actual transparent macro implementations and
reproducible expanded raw manifests/listings, or inline them. The source-closure
proof must consume those exact reviewed values. A semantic macro contract may
hide routine proof ceremony from an application author; it may not hide the
only implementation body from the corpus being reviewed.

### 2. [P0] Cube's Win64 callback cannot address the state it mutates

`state` is a packed object in the entry routine's stack frame
(`Spikes/5_Spinning_Cube/SourceClosure.lean:94-124`, especially line 97). Its
address is passed only as `CreateWindowExW`'s creation parameter
(`Spikes/5_Spinning_Cube/Assembly.lean:170-171`). `wndproc` neither handles
`WM_NCCREATE`, recovers `CREATESTRUCT.lpCreateParams`, stores `GWLP_USERDATA`,
nor otherwise obtains that pointer. It nevertheless accesses `state.width`,
`state.height`, `state.resize`, `state.exit`, and `state.hwndOwned` from a
distinct callback stack (`Assembly.lean:187-221`). An entry-frame symbolic
offset cannot denote the corresponding object relative to the callback's
`rsp`.

**Failure fixture:** deliver `WM_SIZE` synchronously during `CreateWindowExW`, as
Win32 permits. The callback writes through no recovered state pointer; the
entry's state remains unchanged or unrelated callback-stack memory is damaged.

**Required closure:** on `WM_NCCREATE`, recover the passed pointer and store it
with `SetWindowLongPtrW`; recover it with `GetWindowLongPtrW` on later messages,
adding exact imports, provider protocols and lifetime proof. Alternatively use a
declared static singleton and narrow the product to one window. Prove callback
access remains valid until callback unregistration/window destruction.

### 3. [P0] The displayed Cube source cannot satisfy its own source-closure and frame claims

The host references `vkCreateInstanceName` and `vkCreateInstancePtr`
(`Spikes/5_Spinning_Cube/Assembly.lean:232-240`), but the static table declares
neither; the instance function-name table starts with `vkDestroyInstance`
(`SourceClosure.lean:13-26`). Device creation passes `&swapchainExt`
(`Assembly.lean:264-272`), while the declared pointer array is `deviceExts`
(`SourceClosure.lean:134-135`). These are direct unresolved-symbol
counterexamples to `cubeSourceHasNoUnresolvedForms` (`SourceClosure.lean:176-178`).

The frame also declares none of `emptyVertexInput`, `lineList`,
`oneDynamicViewport`, `lineRaster`, `sample1`, `colorAttachment`, `opaqueBlend`,
`dynamicStates`, or `viewportScissor`, although all are passed to graphics
pipeline creation (`Assembly.lean:371-380`) and the design says they are
materialized host-frame structures (`SPIKE_5.md:1503-1534`). The two
`shaderStages` records are allocated in the frame but never visibly populated
after module creation (`Assembly.lean:299-312`).

**Required closure:** declare every static symbol and every authored or
macro-demanded frame object; initialize every nonzero Vulkan structure and both
stage records; pack their dependent frame demands; and prove all symbolic
addresses resolve exactly once with nonoverlapping lifetimes. Add mutations for
each missing name/object before reinstating the empty-unresolved-form theorem.

### 4. [P0] A pre-ready worker-creation failure publishes `.ready`

On `CreateThread` failure the source sets failure status and `shutdown`, then
jumps to `resume_workers` (`Spikes/4_Web_Server/Assembly.lean:64-82,108-112`).
After resuming the successfully created prefix, `resume_loop` unconditionally
branches to `publish_ready`, stores `start_gate = 1`, and only then enters the
shutdown service/join path (`Assembly.lean:84-105`). This contradicts the stated
requirement that pre-ready worker failure never publishes readiness and
discharges acquired resources before a nonzero exit
(`docs/WEB_SERVER.md:88-90`).

**Required closure:** split successful startup from failure unwinding. Resume a
created suspended prefix only through a failure gate which cannot publish
readiness or serve; join/close that prefix, unregister the console handler,
close the listener, end Winsock and exit nonzero. Add a failure fixture for each
creation index and for `ResumeThread` failure.

### 5. [P0] The unconditional eventual-RST theorem is false under the accepted frame rule

`streamResetCancelsOnlyAddressedIncarnation` concludes an eventual exact
`RST_STREAM` from only a cancellation request
(`Spikes/4_Web_Server/Cancellation.lean:260-266`). The accepted policy requires a
stream cancellation to finish an already partially emitted frame before that
reset; only connection teardown may dispose the suffix
(`docs/WEB_SERVER.md:143-149`; `Cancellation.lean:274-282`). If a peer stops
accepting bytes after a positive partial send, the suffix cannot finish. A
connection timeout/failure may lawfully close it, in which case no RST is put on
the wire.

**Required closure:** state the real result:
`finishCurrentFrameThenRst ∨ connectionTeardownWithExactSuffixDisposition`.
Derive the first branch only under named fairness, writable-peer and
connection-survival premises. Keep the connection-timeout escalation theorem
separate.

### 6. [P0] Spike 4 assigns interruption semantics to provider calls its machine never interrupts

The cancellation construction uses `interruptibleCall` for poll, receive, send,
accept and `Sleep` (`Spikes/4_Web_Server/Cancellation.lean:31-54,161-185`). The
selected program instead uses nonblocking sockets, bounded `WSAPoll`, ordinary
bounded `Sleep`, and a console callback which merely stores `shutdown`
(`Assembly.lean:100-106,164-168,183-226`). It imports no cancel operation. The
standard-library rule requires an interruptible foreign call to name the
provider interrupt, result/cancel race, returned custody and late-result handling
(`docs/STDLIB.md:218-228`). No such machine action exists here.

**Required closure:** model these selected calls as bounded uncancellable calls
followed by an actual cancellation observation point. Reserve
`interruptibleCall` for an IOCP/event/CancelIoEx-style realization whose exact
provider cancellation protocol is in the platform plan and source.

### 7. [P0] The cancellation CFG map is neither operational nor total

The map calls `preface_loop`, `frame_parse_loop` and `connection_draining`
cancellation points (`Spikes/4_Web_Server/Bindings.lean:24-48`). At
`frame_parse_loop` the machine immediately parses/dispatches, and
`connection_draining` is only an unconditional jump
(`Assembly.lean:310-345,557-558`). Neither observes a pending request, consumes
its affine authority, or transfers control to a disposition. A custody-safe
state is not by itself a cooperative cancellation point.

The purported whole-server map also omits material blocks and loops including
`create_workers`, `resume_loop`, `service_loop`, `join_workers`,
`console_handler`, accepted-connection setup/failure and `send_positive`
(`Assembly.lean:64-168,219-238,514-522`). In particular the root cancellation
summary is claimed by the final server facet while its actual service loop is
not mapped.

**Required closure:** distinguish safe-state predicates from machine
cancellation-observation/control-transfer edges. Require total post-expansion
basic-block and edge classification, with explicit setup, callback, fault,
cleanup and no-return cases. Add actual request polls/branches at every mapped
logical cancel point and reject every unmapped reachable block.

### 8. [P0] The selected resource snapshot still permits unrelated axis semantics

`SelectedResourceSemantics` stores `requiredAxes` and its `axes` function
separately from `capabilities`; `fromConstruction` mentions only
`capabilities` (`docs/SEMANTICS.md:159-165`). No displayed equality says the
selected axis operations, limits, exhaustion or lifecycle values are the entries
of that captured dictionary. A constructor can therefore snapshot one
capability dictionary while supplying different axis semantics.

**Required closure:** use one finite dependent capability map. Derive
`requiredAxes` from its keys and every selected axis by proof-indexed lookup.
Make construction provenance a property of that entire map, not a neighboring
field.

### 9. [P0] `ProcessNormalization` is ill-typed and can recapture resource semantics

The displayed structure has only `network`, `denotationExact`,
`requirementsExact`, and `realizationTransport`
(`docs/REFINEMENT.md:177-183`). Its `.shape` definition projects nonexistent
`normalization.processSpecification` and `normalization.processShape`
(`REFINEMENT.md:185-188`). Moreover, the source type of `realizationTransport`
reconstructs `Specification.fromBody`, which invokes a fresh ambient
`CapturesResourceSemanticsFor` instead of being indexed by the original
`spec.resourceSemantics`.

**Required closure:** store an explicit normalized specification, equality of
its resource snapshot to the original snapshot, body/denotation and requirement
transport, and the process-shaped witness as actual fields. Construct the
normalized value using the retained snapshot directly; do not rerun instance
search.

### 10. [P0] Portable staged closure erases its provenance, and the proposed fixture supplies names rather than evidence

`PartialProcessRealization.close` now consumes the exact partial value, but
returns a plain `ProcessRealization spec` (`docs/REFINEMENT.md:226-231`). Its
`ProcessPlanSource` has only `sequential` and `explicit` origins
(`docs/PROCESS.md:1351-1369`), so it cannot retain the exact blended graph as
`PROOF_FEASIBILITY.md:892-907` claims or dependently determine the later machine
closed scopes.

The new staged file does not falsify this interface. Its cube- and engine-specific
boundary, completeness, coherence, resource, progress, commutation and rejection
witnesses are undeclared single-use identifiers throughout
`Spikes/5_Spinning_Cube/Staged.lean:9-101,131-188`. The feasibility document
admits that the future theorem has not compiled (`PROOF_FEASIBILITY.md:941-946`).

**Required closure:** introduce a dependent `ClosedBlend` or a blend constructor
in `ProcessPlanSource` retaining the exact graph, local certificates and closure
proof. Index platform closed scopes and `MachineBlend` by that value. Then make
the staged fixture elaborate against actual definitions, including the required
negative mutations; a list of desired theorem names is not closure evidence.

### 11. [P0] The mandatory million-to-tens-of-millions proof-economics gate has no evidence

The acceptance rule requires one-million and ten-million-plus instruction
fixtures, at least one thousand boundary shapes, heterogeneous instruction and
process/resource structure, plus clean and incremental work counts
(`docs/PROOF_FEASIBILITY.md:755-784`; `docs/REFINEMENT.md:603-637`). No such
fixture, manifest, execution report or measurement exists in the corpus. The
current small design spikes cannot falsify flat normalization, global manifest
reconstruction, import explosion, or whole-source kernel reduction.

Cube already exposes the likely failure mode: whole-expansion `decide` proofs
for unresolved forms and manifest equality
(`Spikes/5_Spinning_Cube/SourceClosure.lean:176-182`) ask the kernel to traverse
the aggregate source. That is not a demonstrated hierarchical closure path for
tens of millions of instructions.

**Required closure:** add reproducible generated 1M and 10M+ corpora, retained
machine-readable `LocalityContract`, `InvalidationPlan` and
`BuildExecutionReport` artifacts, and boundary-preserving mutations with actual
elaboration/kernel/cache counts. Source closure must aggregate proved per-macro
and per-shard manifests hierarchically; it must not normalize a monolithic
listing for every leaf edit.

### 12. [P1] `exportedContract` adds ceremony but the facet bridges discard its exactness witness

`toCooperativeTerminationFacet` derives `exactSummary` and never uses it before
returning `.cooperative contract`; the supervised bridge likewise returns the
bare contract (`docs/PROCESS.md:1153-1171`). The `TerminationFacet` constructors
accept `ProcessTerminationContract` directly (`PROCESS.md:1087-1097`). Thus the
summary-export equality is neither needed to prevent manufacturing liveness—the
contract already contains `reachesSafePoint`—nor retained to connect the facet
to `pendingCustody`, the exact affine request occurrence, or incarnation.

**Required closure:** choose one source of truth. Either make the facet carry
`ContractExactlySummarizesCancellation summary ...` and use it in cancellation
transitions, or remove `exportedContract` and construct the self-contained
termination contract directly. Do not make authors prove and consumers store an
exactness bridge which vanishes at the only conversion point.

### 13. [P1] The HPACK cancellation theorem does not distinguish committed and working decoder states

`hpackCancellationPreservesLastCommittedState` takes one `DecoderState state`,
assumes `CancellationDuringDecode state`, and promises cancellation with that
same state (`Spikes/4_Web_Server/Cancellation.lean:284-288`). The requirement
distinguishes the last committed decoder state from mutable in-slice working
state (`docs/WEB_SERVER.md:134-139`). The theorem as written either blesses a
mid-mutation value or hides the essential rollback/commit relation inside an
opaque predicate.

**Required closure:** quantify `committed` and `working`, relate slice start and
mutation to them, and prove cancellation returns exactly `committed` or finishes
the slice and returns a separately named committed successor.

### 14. [P1] Shutdown repeatedly enqueues GOAWAY without a visible idempotence or failure law

Every visit to `connection_schedule` with global shutdown set invokes
`h2_enqueue_goaway`; `connection_shutdown` invokes it again, and neither call
checks a result (`Spikes/4_Web_Server/Assembly.lean:265-272,553-558`). The control
queue is bounded to 32 entries (`Resource.lean:17`). The macro alias
`beginGracefulShutdown` (`Macros.lean:114-115`) does not expose at the call site
that repeated use consumes no slot, preserves the frozen last-stream prefix, or
cannot fail.

**Required closure:** carry an explicit `goawayPublished` state and take one
enqueue transition, or expose a proved idempotent result which the caller checks.
Prove the drain loop makes progress or reaches its close/escalation frontier.

### 15. [P1] Resource parametrization and concrete-axis identity remain incomplete

The generic `webServerSpec resources` uses global `behaviorPolicy`, which in turn
hardcodes the selected global `resourcePolicy` for HPACK limits
(`Spikes/4_Web_Server/Spec.lean:13-33,45-67`). Instantiating the generic function
with a resource model having a different table limit does not change that
behavior. This defeats the advertised reusable resource-parameterized spec
family even though the currently selected instance happens to agree.

At the realization junction, `ResourceAxisRealization` takes an abstract axis
but chooses an unrelated `metricAxis : metric.Axis`; no displayed key equality
connects them (`docs/PROCESS.md:1288-1309`). Web exports per-stream/per-connection
resident bounds and root socket/handle bounds, but no whole-server resident-byte
bound; Hello, Sort and Gzip expose no concise concrete root-resource theorem.

**Required closure:** derive every observable policy limit from the passed and
captured resource semantics. Index the concrete axis by required-axis membership
and an exact injective key mapping. Export one root resource equation/bound per
spike from that mandatory family, with scoped projections where useful.

### 16. [P1] Sort makes erased occurrence stability a precious product demand

The observable success theorem is over input and output `ByteArray`, but
`stableSorted` demands preservation of hidden occurrence ordinals
(`Spikes/2_Sort/Spec.lean:16-27,48-54`). Equal line values serialize identically;
swapping two equal occurrences cannot change the output bytes. The document
itself notes that encoding erases ordinals (`docs/SPIKE_2.md:185-199`). Requiring
stability therefore constrains the algorithm/model proof without constraining
this program's correctness.

**Required closure:** make the precious CLI contract a sorted permutation of
normalized byte lines. Retain stable occurrence identity only as an optional
component theorem or for a future interface which exposes record identity.

## Round 17 fixpoint decision

**No fixpoint.** Round 17 has eleven P0 blockers and five P1 semantic/economic
defects. The process/resource/staged prose improved materially, Section 12 now
states the right finite/infinite obligations, and Sort/Gzip use the correct
model-correctness then assembly-refinement boundary. Those gains do not overcome
missing buildable assembly, false Cube closure, an invalid callback, false HTTP
cancellation claims, nonoperational CFG cancellation mapping, or uncompiled
dependent interfaces. The target-scale proof-economics claim remains wholly
unmeasured. No file other than this review report was edited, and no undeveloped
library was built.

## Round 18 external review (commit `41f5c9c`)

### Scope and repairs verified

This round reread the governing corpus and all five spikes. Independent
fresh-context passes covered specification/source closure and Web/Cube; the root
pass integrated them against the total architecture and the new target of one
million to tens of millions of instructions.

No `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` declaration occurs in
the Lean spike sources. The repository is still an interface corpus: `Grass/`
has no library sources and there is no Lake project file, so the terms cannot be
elaborated here and Lean cannot rescue the type inconsistencies below.

Several repairs are material. Selected resources now come from one finite,
injectively keyed construction snapshot (`docs/SEMANTICS.md:159-184`).
`ProcessNormalization` retains resource, body, requirement, presentation, and
realization transport evidence (`docs/REFINEMENT.md:191-208`). `ClosedBlend`
retains its partial graph, closure, provenance, and exact origin
(`REFINEMENT.md:246-266`). Cube's callback now installs, recovers, and clears its
state (`Spikes/5_Spinning_Cube/Assembly.lean:188-266`;
`SourceClosure.lean:302-317`). Web's startup split, conditional RST disposition,
bounded provider summaries, total top-level CFG classification, captured policy,
and GOAWAY idempotence are also real improvements.

### 1. [P0] `SpecificationLanguage` is not a well-scoped Lean interface

The class quantifies only `Syntax`, but `denote` returns `ContractFragment
resources`, where `resources` is unbound
(`docs/SPECIFICATION_LANGUAGES.md:23-26`). `SomeSpecComponent resources` then
stores `SpecificationLanguage Syntax` without connecting the denotation to that
selected value (`SPECIFICATION_LANGUAGES.md:28-33`).

**Required closure:** index the language by the resource carrier and selected
value, or make denotation explicitly polymorphic with the required coherence
law. Elaborate two heterogeneous language instances and their suite together.

### 2. [P0] The precious root captures the supposedly replaceable presentation

The prose says internal states, ports, and decompositions remain replaceable
(`docs/SPECIFICATION_LANGUAGES.md:99-109`). `SpecProcess` nevertheless stores
`State`, `Event`, `Command`, `Outcome`, transition relations, channels, custody,
and progress (`docs/SEMANTICS.md:186-203`). `capture` selects these through an
ambient `CapturesSuiteAsProcess` instance and copies them into the precious value
(`SEMANTICS.md:226-260`). Two lawful encodings of one suite can therefore create
different indices for all downstream proofs. An unrelated state/channel change
has global invalidation cost.

**Required closure:** keep the suite, selected resource snapshot, exported
contract, and abstract demands precious; move state/channel structure into a
replaceable presentation. Alternatively prove a canonical quotient/uniqueness
law strong enough that capture choice cannot enter downstream indices. Do not
choose precious meaning through ambient instance search.

### 3. [P0] `ProcessRequirement` is orphaned and boundary-unsound

Neither `ContractFragment` nor `SpecificationSuite` carries process requirements
(`docs/SPECIFICATION_LANGUAGES.md:14-21,70-77`), although Sort and Web construct
parser requirements (`Spikes/2_Sort/Spec.lean:33-44`;
`Spikes/4_Web_Server/Spec.lean:45-57`). No displayed generic refinement field
selects a witness and proves `acceptable`, so the promised universal
substitution (`docs/PROOF_FEASIBILITY.md:1138-1167`) has no end-to-end carrier.

The structure also stores `boundary` beside an arbitrary `acceptable :
SpecProcess resources -> Prop`, with no law that an acceptable witness has that
boundary or a compatible resource snapshot
(`SPECIFICATION_LANGUAGES.md:115-123`). It can advertise A and accept B.

**Required closure:** add a finite keyed dependent demand family through
fragments, suite, root, and refinement. Index witnesses by the required boundary
and resource view, and make every spike name the selected witness,
acceptability proof, and occurrence-exact substitution.

### 4. [P0] Both staged fixtures contradict the repaired staging API

`ofNetwork` and `ofProtocol` require resource-snapshot equality as well as
denotation and requirement equality (`docs/REFINEMENT.md:168-189`); the Cube
calls provide only the latter two (`Spikes/5_Spinning_Cube/Staged.lean:6-9,
130-133`). `close` returns `ClosedBlend`, but both fixtures annotate its direct
result as `ProcessRealization spec` (`Staged.lean:76-79,182-183`), discarding the
wrapper which program closure is expressly required to retain
(`REFINEMENT.md:288-293`).

**Required closure:** pass the resource proof, retain each named `ClosedBlend`,
and project `.realization` only at APIs which need it. Put these files in an
elaborated fixture before revising the prose further.

### 5. [P0] The fragment interfaces disagree and cannot carry the stack claims

The documented `VerifiedFragment` fields are `source`, `expanded`,
`expansionExact`, `localCorrect`, and `citations`
(`docs/ASSEMBLY_CONSTRUCTION.md:204-210`). Web constructs that type with a field
named `certificate` and drops citations (`Spikes/4_Web_Server/Macros.lean:15-20`).

More deeply, the shown type has one ordinary Hoare exit and no effect/exit
family. It cannot carry the claimed provenance non-escape, obligation disposal,
cancellation/fault/interruption exits, probe/overflow behavior, restoration on
every edge, or unwind laws (`ASSEMBLY_CONSTRUCTION.md:241-283`). No spike invokes
`withStack`, so none of these laws is falsified by a maintained fixture.

**Required closure:** define and use one interface with indexed normal and
exceptional exits. Make `withStack` a scope eliminator whose result cannot
mention its fresh provenance, and add positive and rejection fixtures for
escaping borrows, jumps, finalization, cancellation, and bounded dynamic use.

### 6. [P0] Web still contains semantic pseudoverbs instead of complete assembly

`LocalFragmentBody` has a computed `rawExpansion`, but its bodies use whole
algorithms such as `exactStaticOrDynamicLookup`, `transitionBy`,
`insertAndEvictTo`, and `dischargeOrAdoptEveryStreamObligation`
(`Spikes/4_Web_Server/Macros.lean:92-190,216-274,433-459`).
`serverExpandedListing` is only a projection and no expanded raw instruction
listing is checked in (`SourceClosure.lean:18-34`). The unavailable
`x86_fragment_body` elaborator is thus asked to manufacture missing
implementations and certificates, contrary to the promised authored,
elaborated, and exact expanded review views
(`docs/ASSEMBLY_CONSTRUCTION.md:62-63,120-127`).

**Required closure:** make each operation a genuine finite library constructor
with inspectable expansion and local theorem, or check in the selected raw
expansions and manifests. Naming a projection `rawExpansion` is not evidence
that the instructions exist.

### 7. [P0] Legal fragmented Web HEADERS contradict the helper precondition

`continuationBody` requires frame type `CONTINUATION`
(`Spikes/4_Web_Server/Macros.lean:111-121`), but the host calls it from a
`HEADERS`/not-`END_HEADERS` path (`Assembly.lean:387-403`). A legal first fragment
must violate the helper contract or be rejected.

**Required closure:** separate beginning a header block from appending a
CONTINUATION, or parameterize and prove the permitted initial transition and
connection-exclusive continuation state.

### 8. [P0] Web dispatches payload after proving only the header exists

`parseFrameHeaderBody` requires nine bytes and publishes a payload pointer
(`Spikes/4_Web_Server/Macros.lean:34-47`). The host then dispatches, debits flow
credit, decodes HPACK, and consumes payload with no visible complete-payload or
`NEED_MORE` branch (`Assembly.lean:350-459`); the HPACK call checks only
`HPACK_CONNECTION_ERROR` (`Assembly.lean:413-426`).

**Required closure:** return a proof that the full declared payload is resident,
or handle `NEED_MORE` from every consumer before any protocol, credit, or
decoder-state mutation.

### 9. [P0] Flow-blocked Web cancellation has no operational consumer

`h2_cancel_expired_streams` only publishes a cause
(`Spikes/4_Web_Server/Macros.lean:333-340`). The only visible
`h2_observe_writer_cancellation` is in the send-suffix loop after writable
readiness (`Assembly.lean:534-545`). A stream with no current frame or zero DATA
credit is excluded by `h2_has_sendable_outbound` (`Macros.lean:285-301`), so it
returns to polling without reaching the observation/RST path. This contradicts
`blockedFlowControlRemainsCancellable`
(`Cancellation.lean:338-342`).

**Required closure:** add a scheduler-level cancellation consumer which enqueues
RST without DATA credit when no frame is in flight. Preserve finish-current-
frame behavior only for an already serialized prefix and map the new block to
the cancellation summary.

### 10. [P0] Cube's swapchain storage and recreation counters are incomplete

The host allocates `imageCount * (8 + 8)` bytes into `imagesAndViews`, then uses
separate `images`, `views`, and `imageInitialized` pointers
(`Spikes/5_Spinning_Cube/Assembly.lean:409-425,522-528`). Source closure declares
them as unrelated pointer objects, but no code partitions the allocation or
allocates/zeros the bitmap (`SourceClosure.lean:138-141`). Also,
`swapchainRetirementBody` destroys entries without resetting
`initializedViewCount` or `viewIndex` (`Macros.lean:286-309`); recreation then
uses those stale counters (`Assembly.lean:414-426`).

**Required closure:** provide a typed aggregate with proved slices plus a sized,
zeroed bitmap, or independent checked allocations. Reset both counters after
retirement and prove all indices against the new image count.

### 11. [P0] Cube publishes device ownership too early and cannot clean partial dispatch

The host sets `deviceOwned := 1` after physical-device enumeration, before
`vkCreateDevice`, with no success-site publication
(`Spikes/5_Spinning_Cube/Assembly.lean:294-318`). Selection failure can therefore
clean a nonexistent device. Dispatch resolution may subsequently fail after any
missing slot (`Macros.lean:155-170`), while reverse cleanup calls
`vkDeviceWaitIdle` and other device functions whenever that same flag is set
(`Macros.lean:318-345`), including unresolved slots.

**Required closure:** publish ownership only after successful creation, track
dispatch completeness separately, and make partial cleanup use only established
capabilities. Prefer validating a private table before atomic publication.

### 12. [P0] Cube's claimed closed source has an unresolved branch

`surfaceSelectionBody` jumps to `fail_runtime_free_formats`
(`Spikes/5_Spinning_Cube/Macros.lean:240-257`). That label occurs nowhere else
and is absent from `cubeReviewedBlocks` (`SourceClosure.lean:243-252`). This
directly falsifies `rawCubeHost.unresolvedForms = #[]` and the exact
manifest/symbol claims (`SourceClosure.lean:285-295`).

**Required closure:** add the free-and-fail block or an explicitly owned typed
external edge. Retain a negative fixture showing that deleting any target makes
closure fail.

### 13. [P0] The required million/tens-of-millions gate is unpassed

The new criterion correctly requires reproducible 1M and 10M instruction
corpora, heterogeneous boundaries, clean/incremental measurements, and a
boundary-preserving leaf mutation (`docs/PROOF_FEASIBILITY.md:775-801`). It then
accurately says none of those corpora or reports exists
(`PROOF_FEASIBILITY.md:803-814`; `docs/REFINEMENT.md:727-733`). No checked-in
`LocalityContract`, `InvalidationPlan`, or `BuildExecutionReport` value exists.
That honesty avoids an overclaim but remains a release/fixpoint blocker.

**Required closure:** check in deterministic generators, machine-readable clean
and incremental reports, memory/proof-term measurements, and retained
invalidation plans at both sizes. A boundary-preserving leaf edit must
re-elaborate and kernel-check only the leaf and its ancestor path.

### 14. [P1] Source closure mixes phases and is not instantiated uniformly

Every governing `SourceFragmentClosure` contains a
`FragmentMachineCertificate` (`docs/REFINEMENT.md:594-601`), although the source
phase is said not to claim refinement (`REFINEMENT.md:429-430`). Thus changing a
behavior theorem invalidates syntactic expansion/reference closure. No spike
constructs `SourceFragmentClosure`, `SourceClosureNode`, or
`HierarchicalClosedAsmSource`: Cube uses flat whole-array `decide`, Sort/Gzip use
flat closure, and Web uses a separate custom hierarchy. This does not bank proof
work at target scale.

**Required closure:** separate syntactic expansion/reference closure from
behavior certificates and pair them by exact expanded-leaf identity. Make all
spikes use the same governing tree and measure source, behavior, and artifact
invalidation separately.

### 15. [P1] Assembly proof automation is not economically auditable

Major theorems still end in bare `verify_asm`/`verify_asm_model` calls (Hello
`Spikes/1_Hello_World/Assembly.lean:74-76`, Sort/Gzip Bindings, Web
`Bindings.lean:6-22`, Cube `Assembly.lean:663-667`). Calls expose neither
certificate inputs nor a residual-goal allowlist/report. The prose forbids
invariant discovery and policy choice inside the tactic
(`docs/DECISIONS.md:460-465`), but the rule is not falsifiable.

**Required closure:** specify the tactic's exact input/output contract, emit a
stable consumed-certificate/residual-goal manifest, and add fixtures where
missing invariants, provider cases, and semantic correspondences remain open.
Report tactic time and proof-term size per shard.

### 16. [P1] Reuse and author ergonomics retain three avoidable hazards

Every child presentation must equal the entire root resource snapshot
(`docs/REFINEMENT.md:158-166`), preventing reusable components from selecting an
exact subset without depending on unrelated axes. Use exact restriction maps
and prove their union equals the root demand.

`StructLayout` has no uniqueness invariant for `FieldSpec.name` and no proved
name lookup (`docs/ASSEMBLY_CONSTRUCTION.md:141-153`), so stable named paths may
be ambiguous. Require unique names and lookup exactness.

Finally, spikes apply `withLiveness`, `withProgress`, and `withOutcomes` after
suite capture (for example Sort `Spikes/2_Sort/Spec.lean:48-51`, Web
`Spikes/4_Web_Server/Spec.lean:61-68`). Since the root contract must be derived
from its retained suite (`docs/SPECIFICATION_LANGUAGES.md:86-103`), these
combinators must visibly append DSL fragments and recapture with an exact
theorem, not mutate a second semantic owner.

## Round 18 fixpoint decision

**No fixpoint.** Round 18 has thirteen P0 blockers and three P1 groups. The
resource, normalization, blend, callback, and Web lifecycle changes are genuine
monotonic improvements. The total system still has ill-scoped and inconsistent
central interfaces, precious capture of replaceable topology, orphaned
existential demands, non-elaborating staged fixtures, absent reviewable assembly,
and concrete Web/Cube execution defects. The 1M/10M proof-economics test is the
right gate, but it is explicitly unexecuted. No file other than this report was
edited, and no undeveloped library was built.
