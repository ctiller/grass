# Historical process-design audit

Status: design-steward audit record at `origin/main`
`254f3a1db2b85f2568bd5b7de4e3f0913bf1883e`.

This note disposes the thirteen historical `c-process` commits named by
`e-auditor:20`. It is evidence about provenance and current implementation
coverage; it does not own process semantics and cannot override
[PROCESS.md](PROCESS.md), [PROCESS_SHARDING.md](PROCESS_SHARDING.md),
[SEMANTICS.md](SEMANTICS.md), or [REFINEMENT.md](REFINEMENT.md).

The audit is deliberately not a blanket retrospective ratification. A row
ratifies only the semantic proposition it names. It does not ratify unrelated
code, implementation-plan prose, commit authorship, or stronger claims suggested
by a commit title. “Rebuilt” means the intent survives through a different
current interface. “Defective” means the current checked-out normative surface
still contains a contradiction or an unimplemented public claim.

## Disposition

| Historical commit | Disposition | Narrow result and current evidence |
|---|---|---|
| `c373340b` | **Ratified** | Shared-region movement is a plan concern, not a field added to precious `ProcessSpec.Step`. Current `ProcessPlan.sharedUpdate` and `sharedUpdatePreserves` bound each local move; `StepsLocally.sharedWritesAdmitted` consumes the bound; `sharedInvariantHolds_preserved` and `wellFormed_preserved` carry it through a network step. `Tests/Process/ProcessStepFixtures.lean` exhibits both an admitted counter update and rejection of an unproved update. |
| `5a3b6d3b` | **Ratified narrowly** | A send requires the named sender incarnation to be live. Current `SendsEscrow.senderIsLive` is consumed by the transition family, and `Tests/Process/ChannelStepFixtures.lean` constructs the dead-sender attack and derives its contradiction from that field. The commit title's broader statement about acceptance is not ratified by this row; current `ProcessAcceptance` separately and explicitly marks its predicates as specification-owned input. |
| `d6027c7c` | **Ratified; staging prose rebuilt** | Interruption is indexed by the exact abandoned demand: current `ProcessVocabulary.InterruptReason : Demand -> Type`, `ProcessEvent.interrupted`, `ProcessLifecycle.interrupted`, and `EndsInstance.endingIsEarned` retain that index. `Tests/Process/DeliveryFixtures.lean` proves one demand interruptible and another empty; `Tests/Process/EndingFixtures.lean` attacks an ending not earned by the instance. The old facet-staging paragraph has been replaced by the more exact target/open-gate account now in `PROCESS.md` §3. |
| `058957a2` | **Rebuilt** | The cancellation predicates survived as checked library definitions rather than prose-only sketches: `CancellationPolicy.Covers`, `RegionsDeclared`, and `PointsDeclared`, with all three fields required by `ScopedCancellationCertificate`. `CancellationPolicy.not_covers_of_unclassified` and `Tests/Process/CancellationFixtures.lean` reject reuse of a policy after a new blocking call is discovered. |
| `38c056ef` | **Rebuilt** | The author-facing forwarding intent is preserved without wrapper accessors. Current `ProcessPresentationNetwork` is an abbreviation for `StructuralProcessNetwork (SpecProcess resources)`, so `RoleSchema`, `protocol`, `Instance`, `instanceOf`, and `schemas` are definitionally available. The historical record-shaped wrapper no longer exists. |
| `103aa2bb` | **Still defective on the audited snapshot** | Selecting a trace separately from structural topology is retained as `SelectedProcessTrace`; a network does not own precious behavior. But current `REFINEMENT.md` still asks `SubsystemRealization.refines` for nonexistent `shaped.network.instances` although `StructuralProcessNetwork` exports `instanceOf`. Candidate `67f5ceb971156133b92bfce7a668e0aad24c4492` repairs this by adding an instance-indexed abstract behavior, exactness to the actual `instanceOf` value, and refinement of that behavior. This row remains defective until an independently reviewed repair reaches `main`. |
| `8e1f2316` | **Ratified target; implementation gate open** | The low-ceremony split is still the intended design: `ProcessTopologyCore` carries universal graph/channel/spawn structure; the unqualified `ProcessTopology` carries exactly the cancellation and supervision facets demanded by the selected boundary. Current Lean implements `ProcessTopologyCore`, while `ProcessPlan.topology` still has that weaker type. `PROCESS.md` labels this state provisional and excludes it from a complete `VerifiedProgram`; therefore the missing aggregate is visible incompleteness, not silently accepted equivalence. |
| `3a37e2ed` | **Ratified and strengthened** | Fault, violation, and interruption classes remain per-vocabulary rather than a closed global sum. Current `ProcessVocabulary` carries all three, and `InterruptReason` has since been strengthened to depend on the abandoned demand. `Tests/Process/DeliveryFixtures.lean` checks total cross-vocabulary classification and an empty target class. |
| `b88b0136` | **Ratified structurally; presentation connection defective as above** | There is one implemented neutral shape, `StructuralProcessNetwork`. It carries roles, their finite complete/distinct schema list, protocols, instance identities, and `instanceOf`, but no behavior oracle. `Tests/Process/StructuralNetworkFixtures.lean` has negative elaboration fixtures for the removed `denotation`, `traceDenotation`, `exact`, and `channels` fields. The later Semantics-side connection is covered by the `103aa2bb` disposition rather than being inferred from this structural success. |
| `fa138b3b` | **Rebuilt and ratified** | Cancellation is scope-indexed and optional. `Grass.Process.Cancellation` exposes the bounded author facet without importing network topology; `Tests/Process/FacadeCancellationFixtures.lean` checks that `ProcessPlan`, `ChannelContract`, `NetworkAssertion`, `EscrowLedger`, and `ProcessTopologyCore` do not leak through that import. `ScopedCancellationCertificate.composePolicy_covers` composes local coverage rather than introducing a second whole-plan policy type. |
| `d58299ea` | **Split disposition** | `EffectDemand boundary := boundary.Demand` and demand-indexed `EffectResult` are ratified and implemented in `Grass/Process/Sequential/Machine.lean`; no wrapper identity was introduced. The same commit's plan-indexed cancellation sketch was superseded by the scope-indexed `CancellationPolicy` and certificate family audited under `fa138b3b`. |
| `3c5e2eb0` | **Ratified relocation; index edit superseded** | Neutral `ScopeId` and `DriverBoundary` live under `Grass.Specification`, below Process. `Tests/Process/LayeringSpecificationOnly.lean` imports only `Grass.Specification.Boundary` and negatively checks that Process declarations are unavailable; `Tests/Process/LayeringFixtures.lean` exercises the Process-to-Specification dependency direction. Removing the old implementation-plan entry from `docs/README.md` is superseded by the repository's separate non-normative roadmap policy, not treated as a semantic decision. |
| `9709f7f0` | **Ratified implementation; index edit superseded** | The graph/exposure seam remains in `Grass/Process/Network/Graph.lean` and `Exposure.lean`; it is part of the current `ProcessTopologyCore` construction. Its temporary addition of `PROCESS_IMPLEMENTATION_PLAN.md` to the normative corpus index was reversed by `3c5e2eb0` and carries no present authority. |

## Current residuals

The audit leaves two deliberately distinct open states:

1. **A live normative defect:** `REFINEMENT.md`'s nonexistent `network.instances`
   projection. The named successor above must be reviewed and merged, or an
   equivalent repair must replace it. Structural-network success is not evidence
   that this Semantics-side connection is sound.
2. **A declared implementation gap:** the facet-carrying `ProcessTopology` and
   its aggregate cancellation/supervision theorems do not yet exist in Lean.
   `PROCESS.md` already prevents the weaker `ProcessPlan` from reaching the
   complete-program gate. This audit does not waive that gate.

Everything else in the historical set is accepted only through the exact
current declarations and adversarial fixtures listed above. If those names are
later rebuilt, this note remains history; the owning normative documents and
new checked evidence decide the replacement.
