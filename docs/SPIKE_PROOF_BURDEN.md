# Spike proof-burden ledger

Status: normative pre-implementation accounting. Estimates are smell tests,
not acceptance limits and not claims of measured Lean code.

The exact spike sources intentionally name library theorems and local proof
obligations before those proofs exist. A short identifier is not evidence that
its proof is short. This ledger prices the spike-shaped names that are not
ordinary definitions in the authored directory and prevents proof work from
disappearing behind an optimistic source listing.

The implementation ratchet replaces these estimates with an
elaborator-produced authority report containing declaration identity, normalized
theorem type, owning module, proof-term size, residual goals, dependencies, and
rebuild cone.

## 1. Required classification

Every identifier referenced by authored spike source must resolve to one of:

- `authored-definition`: its body appears in that spike directory;
- `authored-proof`: the application author discharges the exact local goal;
- `library-instance`: a parametric proved constructor is named with its
  arguments and residual goals;
- `generated-structural`: deterministic collection, layout, scope, registry,
  or record assembly with no semantic choice;
- `authority-model`: a versioned ISA, ABI, API, protocol, or format theorem; or
- `unresolved`: a design or implementation failure.

The future `grass spike authority-report` command rejects unknown identifiers
and emits all six categories. A family entry below expands to the exact names
listed; “the usual invariants” is not accepted.

| Burden | Expected work after reusable automation |
|---|---|
| S | constructor application or local first-order VC; normally a few authored lines |
| M | loop/representation induction or finite algorithmic lemma; tens to low hundreds |
| L | novel concurrent coupling invariant or simulation; hundreds and possibly more |
| X | research risk whose residual-goal volume must be measured before reuse is claimed |

## 2. Spike 1

| Exact name | Burden and owner | Proof shape |
|---|---|---|
| `write_all_loop(payload)` | S, library-instance | Standard partial-write induction over the derived payload suffix; author selects operand and failure policy. |
| `helloVerified` closing obligations | S, generated-structural plus authored boundary theorem | Source closure, Win32 provider selection, PE construction, and standard certificate composition are derived; exact-message observation is precious. |

No application-specific algorithmic invariant is hidden in Spike 1.

## 3. Spike 2

`CompareEntry`, `CompareExit`, `FlushOutputEntry`, and `FlushOutputExit` are
generated-structural defaults: typed operands, derived effects/clobbers, and
declared exit meanings. An author may strengthen them; the elaborator may not
invent a stronger semantic invariant.

| Exact name | Burden and owner | Proof shape |
|---|---|---|
| `growable_input_vec` | M, authored-proof | Allocation/capacity/initialized-prefix representation, failure, and provenance transfer. |
| `count_lf_prefix` | M, authored-proof | Induction over scanned input bytes. |
| `represents_scanned_prefix` | M, authored-proof | Descriptors represent exactly the parsed line occurrences. |
| `stable_merge_pass(input, lines, scratch)` | M, authored-proof/library-instance | Instantiate banked stable merge with the physical descriptor relation. |
| `stable_merge_cursors(i,j,k)` | M, authored-proof | Cursor bounds, stable choice, and output-prefix permutation. |
| `sorted_occurrence_consumer(finalDescriptors)` | M, authored-proof | Emit the final stable permutation exactly once. |
| `buffered_stdout(output_buffer, outUsed, committedPrefix)` | M, library-instance | Standard partial-write consumer plus local buffer representation. |
| `stableSortModelCorrect` | authority-model | Banked algorithm theorem, independent of x86 placement. |
| `sortAssemblyRefinesModel`, `sortComponentBinding` | M, authored-proof | Physical scopes and representations refine parser/sort and discharge the keyed component demand. |

## 4. Spike 3

| Exact name | Burden and owner | Proof shape |
|---|---|---|
| `collecting_block(state, capacity=32768)` | M, authored-proof | Input prefix, arena capacity, and block-finalization relation. |
| `crc32_prefix(transferred - remaining)` | S/M, library-instance | Standard CRC prefix theorem for the selected scalar loop. |
| `token_prefix_expands_to_input_prefix(position)` | M, authored-proof | Tokens inflate to the consumed input prefix. |
| `candidates_strictly_precede_position` | M/L, authored-proof | Candidate provenance, bounds, chain order, and certified match contents. |
| `inserted_range(oldPosition, cursor)` | M, authored-proof | Hash-chain update preserves the candidate invariant. |
| `bitAccRep(bitAcc,bitCount)` | M, authored-proof/library-instance | Physical accumulator represents the emitted bit prefix. |
| `SliceConsumerInvariant(output,consumed,outLen)` | M, library-instance | Standard partial-write consumer with gzip output ownership. |
| `fixed32KModelCorrect` | authority-model | Banked RFC-linked compressor/model theorem. |
| `gzipAssemblyRefinesModel`, `gzipComponentBinding` | M/L, authored-proof | Arena representation and callable scope refine the model and requirement. |

The candidate-chain entry must expose content certification as well as ordering;
implementation review rejects the weaker invariant found by external review.

## 5. Spike 4

These `MemoryServerState` members are authored transition data or proofs, not
free library facts:

```text
InitialWithDemands Terminal Step Invariant initialInvariant
initialDemandsWellFormed stepPreservesInvariant terminalAccepts terminalNoStep
desiredAccepts observationsAccept demandsWellFormed progress
```

The HTTP/2 package supplies parametric protocol transitions. The application
still owns route/resource instantiation, root demand routing, and the observation
junction. Before implementation acceptance, expansion prints the complete
instantiated transition relation and invariant; no `MemoryServerState.*` name
may remain unresolved.

Every exact name below is an authored proof unless a generated facet resolver
shows an exact reusable constructor application. The current all-in-one record
is explanatory; [PROCESS_SHARDING.md](PROCESS_SHARDING.md) requires the proofs
to be indexed by their smallest consuming facet.

```text
server_startup_silence
server_fixed_after_ready
server_socket_generation
server_listener_authority
server_admission_permits
server_worker_slots
server_receive_cancel_race
server_send_cancel_race
server_receive_fragments
server_send_prefixes
server_deadline_correlation
server_stream_generation
server_stream_lifecycle
server_continuation_exclusion
server_hpack_state
server_hpack_validity
server_hpack_cancellation_routing
server_flow_credit
server_flow_backpressure
server_control_progress
server_frame_coverage
server_error_scope
server_unknown_extensions
server_no_push
server_priority_ignored
server_settings_order
server_settings_window_rebase
server_ping_payload
server_goaway_prefix
server_output_order
server_stream_cancellation
server_worker_reuse
server_shutdown_custody
server_route_sharing
server_obligation_partition
server_resource_partition
```

| Facet | Burden | Expected argument |
|---|---|---|
| startup/population, first six names | M/L | finite worker/listener induction and generative socket authority |
| I/O/cancellation, next five | L | linearization points for result/cancel races, partial prefixes, deadlines |
| stream/HPACK/flow, through `server_control_progress` | L/X | connection-order induction, private/committed HPACK, two-level credit and backpressure |
| protocol cases, through `server_goaway_prefix` | M/L | case split over the keyed RFC requirement family |
| lifecycle/terminal, remaining names | L | causal output order, reuse, shutdown custody, obligations, resources |

No line-count promise is made. Implementation measures every facet's residual
goals and proof/import cost. If reusable HTTP/2/process theorems do not reduce
these to bounded local coupling arguments, the server proof-economy claim has
failed and the process interface must be revised.

## 6. Spike 5

These names are exact application obligations:

```text
CubeState.InitialWithDemands
CubeState.Terminal
CubeState.Step
CubeState.Invariant
CubeState.render
cube_initial_invariant
cube_initial_demands_are_well_formed
cube_step_preserves
cube_terminal_accepts
cube_terminal_has_no_step
cube_render_depicts_scene
cube_observations_accept
cube_demands_are_well_formed
cube_reactive_progress
cube_frame_productivity
cube_all_subsystem_boundaries_compose
cube_all_requirement_union
```

`CubeState.Step`, `CubeState.Invariant`, and `CubeState.render` are authored
transition data whose expansion must be printed before implementation
acceptance. The pure `cube_*` application proofs are M: induction over close,
Escape, resize, irrelevant input, frame opportunity, commit/coalesce/failure,
and finish. `cube_frame_productivity` is M/L because it consumes explicit
fairness/responsiveness assumptions and lifts through the driver.

`cube_all_subsystem_boundaries_compose` and `cube_all_requirement_union` are
generated-structural only where they rename checked facet certificates. A novel
Vulkan/Win32/GPU coupling condition is an authored L/X residual goal.

Shader semantics, floating-point bounds, Vulkan ownership, and host/shader
connection are charged to their owning realization scopes, not the pure cube
update proof, but remain charged to the complete verified artifact.

## 7. Acceptance and falsification

Implementation acceptance requires:

1. `grass spike authority-report` resolves every identifier and rejects
   `unresolved`;
2. every `library-instance` reports the exact theorem and arguments;
3. every `authored-proof` reports source, residual goals, proof-term size,
   imports, and facet dependencies;
4. weakening each named invariant causes the expected local check to fail;
5. axioms, unchecked certificates, test runs, and digests fail the trust audit;
   and
6. proof-economy tables are regenerated from the report rather than counting
   only visible spike lines.

These estimates are hypotheses to falsify. If HTTP/2 or graphics obligations
expand by orders of magnitude, Grass records that cost and changes the reusable
interface or its proof-economy claim; it does not hide the work in `Grass.Std`.
