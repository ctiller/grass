# Spike 4: multiplexed in-memory HTTP/2 server to Win32 x86-64 PE

Status: design artifact for adversarial review; intentionally not compilable.

Authoring view: agents maintain `Spec.lean`, `Process.lean`,
`Cancellation.lean`, `Macros.lean`, `Assembly.lean`, and `Program.lean`. The
exact snapshot is at the end of this document. Source closure, CFG maps,
bindings, and artifact bundles are generated inspection views.

This spike pressure-tests whether Grass can make a large global event loop
locally provable without hiding either protocol behavior or hand-authored
assembly. It reaches a complete cleartext HTTP/2 prior-knowledge server,
connection and stream processes, RFC 9113 framing and state, RFC 7541 HPACK,
bounded resources, literal/transparent-macro x86-64, and exact PE emission. It
does not build the supporting libraries.

The selected product binds IPv4 loopback port 8080, serves immutable in-memory
routes, admits four active connections and 128 concurrent streams per
connection, uses no TLS and no server push, and allocates no memory after
readiness. It is a reviewable protocol and proof-economy fixture, not an
Internet deployment profile.

The acceptance owner is [WEB_SERVER.md](WEB_SERVER.md). Protocol authority is
RFC 9113 and RFC 7541 as registered in [REFERENCES.md](REFERENCES.md).

## 1. Precious surface

The precious surface is one root `SpecProcess`. Its DSL components state the
HTTP/2/HPACK byte languages, protocol legality, route relation, observations,
failures, progress, and selected resource semantics. Typed junctions capture
them into the root. It does not name listener/connection/stream roles, Winsock,
physical workers, polling, buffer offsets, or x86 registers.

```lean
def body : ByteArray := "Grass web server\n".toUTF8

def routes : Http2Routes :=
  .singleton { method := .GET, scheme := .http, authority := .any,
    path := "/".toASCII, response :=
      { status := 200, fields := [("content-type", "text/plain")], body } }

def behaviorPolicyFor {R} [ResourceModel R] [WebServerResources R]
    (resources : R) : Http2ServerBehaviorPolicy :=
  Http2ServerBehaviorPolicy.fromCapturedResources resources where
    transport := .cleartextPriorKnowledge
    acceptedVersion := .http2
    serverPush := false
    priority := .ignoreDeprecatedSignals
    unknownRoute := .responseStatus 404
    malformed := .rfc9113ScopedError
    unsupportedExtensionFrame := .ignore
    requestMethods := {.GET}
    requestBodies := .discardWithinFlowControl
    responseTrailers := false
    peerSettings := .applyAfterValidationThenAcknowledge
    ping := .acknowledgeOpaquePayload
    goaway := .gracefulPrefix
    connectionWindowUpdates := .rfc9113
    streamWindowUpdates := .rfc9113
    hpackDecoderTableBytes := WebServerResources.hpackDecoderTableBytes resources
    maxHeaderListBytes := WebServerResources.maxHeaderListBytes resources
    initialConnectionWindow := WebServerResources.inboundConnectionWindow resources
    initialStreamWindow := WebServerResources.inboundStreamWindow resources
    hpackEncoder := .anyConformingEncoding
    huffman := .acceptValidRejectInvalid
```

There is deliberately no `message_value` or `message_length`: route bytes and
all lengths are derived from the values. The outgoing HPACK representation is
not precious: peers observe the decoded fields, while exact emitted bytes remain
reviewable through the source/artifact chain. The realization later selects
literal-without-indexing. The decoder is the full bounded RFC 7541 decoder; a
literal-only decoder would not realize the claimed HTTP/2 input behavior.

```lean
def frameFormat : Format Http2.Frame := Http2.frameFormat

def hpackFieldSectionFormat : Format Http2.HeaderList :=
  Hpack.fieldSectionFormat

def frameParserRequirement {R} [ResourceModel R]
    (resources : R) : ProcessRequirement resources :=
  Format.parserRequirement frameFormat

def hpackParserRequirement {R} [ResourceModel R]
    (resources : R) : ProcessRequirement resources :=
  Format.parserRequirement hpackFieldSectionFormat

def webServerSuite {R} [ResourceModel R] [WebServerResources R]
    (resources : R) : SpecificationSuite resources :=
  Http2.memoryServerSuite
    resources routes (behaviorPolicyFor resources)
    (frameParserRequirement resources) (hpackParserRequirement resources)

def webServerSpec {R} [ResourceModel R] [WebServerResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (webServerSuite resources)
    |>.withProgress
      { service := .reactive
        acceptedConnection := .settlesUnder
          [.schedulerFair, .monotonicClockAdvances, .environmentResponsive]
        termination := .under
          [.shutdownEventuallyRequested, .schedulerFair,
           .monotonicClockAdvances, .environmentResponsive] }

theorem webServerSpecCorrect {R} [ResourceModel R] [WebServerResources R]
    (resources : R) : MeetsAllSpecificationTheorems (webServerSpec resources) :=
  Http2.memoryServerSuiteCaptureCorrect
    resources routes (behaviorPolicyFor resources)
    (frameParserRequirement resources) (hpackParserRequirement resources)
```

This theorem is the high-level correctness proof. It is universally quantified
over accepted input bytes, fragmentation, peer settings, windows, scheduler
choices, failures, cancellation, and response interleavings. Assembly does not
replace it; assembly later refines it.

The suite uses a frame/HPACK grammar DSL, HTTP/2 protocol DSL, route relation,
and temporal/resource fragments. Its grammar-to-protocol and
protocol-to-route/observation junctions are precious. It may demand “a process
which realizes this parser format” parametrically; the selected parser witness
and its decomposition are supplied later.

## 2. Resource parameter

The precious specification captures a semantic budget because flow control,
admission, header limits, and deadlines affect behavior. A separate Win32
execution envelope selects workers, OS objects, buffers, scheduling, and fixed
storage and proves it realizes that budget.

```lean
def semanticBudget : Http2ServerSemanticBudget where
  maxActiveConnections := 4
  maxConcurrentStreamsPerConnection := 128
  maxHeaderListBytes := 16384
  hpackDecoderTableBytes := 4096
  hpackEncoderTableBytes := 0
  maxInboundFrameBytes := 16384
  maxContinuationBytes := 16384
  inboundConnectionWindow := 65535
  inboundStreamWindow := 65535
  outboundConnectionWindowCeiling := 2147483647
  outboundStreamWindowCeiling := 2147483647
  streamProgressDeadline := .seconds 5
  connectionIdleDeadline := .seconds 30

def resources : ServerResourceModel :=
  ServerResourceModel.http2 semanticBudget

def spec : SpecProcess resources := webServerSpec resources

def behaviorPolicy : Http2ServerBehaviorPolicy := behaviorPolicyFor resources

def capturedSemanticBudget : Http2ServerSemanticBudget :=
  Http2ServerSemanticBudget.fromCapturedSemantics spec.resourceSemantics

theorem capturedSemanticBudgetExact : capturedSemanticBudget = semanticBudget :=
  SpecProcess.capturedResourceConstructionExact spec

def executionEnvelope : Win32ServerExecutionEnvelope where
  workerCount := 4
  connectionCapacity := 4
  streamCapacityPerConnection := 128
  hpackDecoderStorageBytes := 4096
  maxQueuedControlFramesPerConnection := 32
  maxQueuedDataBytesPerConnection := 65535
  maxReceiveBytesPerConnection := 32768
  maxTransmitBytesPerConnection := 65535
  maxSocketDescriptors := 5
  maxThreadHandles := 4
  pollQuantum := .milliseconds 10
  storage := .fixedAfterReady

def resourcePolicy : MemoryServerResourcePolicy :=
  executionEnvelope.materialize capturedSemanticBudget

theorem executionEnvelopeRealizesSemanticBudget :
    RealizesSemanticBudget executionEnvelope capturedSemanticBudget := by
  simpa [capturedSemanticBudgetExact] using
    Win32ServerExecutionEnvelope.materialize_sound executionEnvelope semanticBudget
```

Memory, active streams, receive bytes, transmit bytes, control-frame slots,
DATA credits, sockets, and Windows handles are distinct axes. A connection
cannot borrow unbounded bytes merely because it owns a socket. Dynamic-table
capacity cannot be repurposed as a decoded-header-list allowance. Capacity
tokens travel through process channels and make backpressure constructive.

Fixed-after-ready means startup constructs every worker, connection, stream,
HPACK, frame, and queue slot before publishing readiness. Startup allocation or
worker creation failure emits no HTTP bytes and exits nonzero after cleanup.
The partial-creation edge never reaches `publish_ready`: it sets shutdown,
resumes the suspended created prefix through `resume_failure_workers`, joins and
closes that prefix, unregisters the console handler, closes the listener, ends
Winsock, and exits nonzero. A `ResumeThread` failure before readiness takes the
declared failed-adoption/no-return boundary rather than waiting on a suspended
thread. Fixtures quantify every creation and resume index.
After readiness the import table has no allocation function, so an allocation
failure transition is unreachable. Admission can still be refused and peers can
still withhold credit; neither is server-owned memory exhaustion.

## 3. Wire and compression model

```lean
def protocolProfile : Http2.Profile where
  transport := .cleartextPriorKnowledge
  maxFrameSize := capturedSemanticBudget.maxInboundFrameBytes
  serverPush := false
  priorityMode := .ignoreDeprecated
  extensionMode := .ignoreUnknown
  hpackDynamicTableBytes := capturedSemanticBudget.hpackDecoderTableBytes
  maxHeaderListBytes := capturedSemanticBudget.maxHeaderListBytes

def connectionModel : Http2.ConnectionModel :=
  Http2.ConnectionModel.server protocolProfile behaviorPolicy routes
```

The model contains the client preface, SETTINGS synchronization, every base
frame type, unknown extensions, stream state, connection and stream errors,
CONTINUATION exclusion, HPACK state, both flow-control levels, GOAWAY prefix,
RST_STREAM, and writer scheduling. Deprecated priority fields are parsed and
validated but cannot affect selection. PUSH_PROMISE is rejected because the
server advertised `SETTINGS_ENABLE_PUSH = 0` and is not a client.

The framing proof surface is deliberately stronger than round-trip testing:

```lean
def frameParserRealizes : ParserRealizes frameFormat
    (Http2.Frame.parseResult protocolProfile) :=
  Http2.Frame.parserRealizesFormat protocolProfile

def hpackParserRealizes : ParserRealizes hpackFieldSectionFormat
    (Hpack.FieldSection.parseResult protocolProfile) :=
  Hpack.FieldSection.parserRealizesFormat protocolProfile
```

These discharge the two existential process requirements after the chosen
parser processes are wrapped around the implementations. They prove complete
success, exact `needMore`, and exact invalid-prefix classification, not only the
success cases below.

```lean
theorem frameWriterRoundTrip (frame : Http2.Frame)
    (admissible : frame.Admissible protocolProfile) :
    Http2.Frame.parse protocolProfile (Http2.Frame.write frame) = .ok frame

theorem frameParserConforms (input : ByteArray) :
    Http2.Frame.parse protocolProfile input = .error ∨
    ∃ frame suffix,
      Http2.Frame.parsePrefix protocolProfile input = .ok (frame, suffix) ∧
      frame.Admissible protocolProfile ∧
      input = Http2.Frame.write frame ++ suffix
```

The second theorem prevents a parser from accepting an unrelated object or
silently dropping a suffix. Stream decoding consumes repeated valid prefixes;
TCP receive boundaries do not enter the HTTP model.

HPACK separately proves integer and plain-string writer round trips and a
decoder conformance theorem:

```lean
theorem hpackDecoderConforms (state : Hpack.DecoderState protocolProfile)
    (block : ByteArray) :
    Hpack.decode state block = .error ∨
    ∃ next fields,
      Hpack.decode state block = .ok (next, fields) ∧
      Hpack.Rfc7541Transition state block next fields ∧
      next.dynamicTable.bytes ≤ capturedSemanticBudget.hpackDecoderTableBytes ∧
      fields.byteSize ≤ capturedSemanticBudget.maxHeaderListBytes
```

`Rfc7541Transition` covers indexed fields, the three literal forms, dynamic
table insertion/eviction, table-size update placement, the 32-byte entry
overhead, integer overflow, string bounds, and static/dynamic index ranges. The
Huffman lemma accepts exactly strings whose bits terminate without EOS and whose
padding is a valid prefix of EOS. Exhaustive table-generation validation and
vendor-independent fuzz probes supplement but do not replace this forall proof.

HPACK mutation is serialized at connection order. Decoded immutable field lists
may then move to stream children. This is why “one decoder per stream” is
rejected even though it would simplify parallel execution.

## 4. Process realization

The replaceable proof lens chooses listener, connection, and stream roles. They
make causal attribution, isolated reset, HPACK connection ordering, and
subtree-resource theorems economical; they are not fields of the root spec.

```lean
inductive ServerRoleSchema
  | listener
  | connection
  | stream

def abstractServer : AbstractSpecificationProcessNetwork resources :=
  Http2.abstractMemoryServer
    (roleSchema := ServerRoleSchema)
    (routes := routes)
    (admission := WebServerResources.connectionCapacity resources)
    (custody := .linearPerConnectionAndStream)

def serverProcessPresentation : ProcessPresentation spec where
  network := abstractServer
  denotationExact := Http2.abstractMemoryServerDenotesContract
  requirementsExact := Http2.abstractMemoryServerRequirementsExact
```

Another presentation may use a single serialized session process or a different
abstract decomposition if it proves the same two exact equations.

The chosen realization is a four-worker fixed pool. Each worker owns at most one
connection at a time; each connection hosts up to 128 logical stream processes,
a connection-local HPACK decoder, and one serialized writer. That topology is
replaceable. A future IOCP realization can prove the same boundary without
changing the spec.

The registry includes root, listener, worker slots, generative connections,
generative streams, HPACK decoder, writer, correlated API calls, and terminal
process. Hoare channel contracts carry:

- positive receive byte chunks plus capacity custody;
- exact unsent suffixes after partial writes;
- frame prefixes and exact residual input;
- ordered HPACK blocks and decoded fields;
- stream creation authority and monotonically fresh identities;
- connection and stream flow credits;
- response requests and output frame custody;
- scoped faults, cancellation, deadlines, cleanup obligations, and terminal
  dispositions.

The principal composition witness is intentionally decomposed:

```lean
structure ServerCompositionWitness where
  startupSilence : BeforeReadyNoProtocolBytesAreEmitted serverProcessPlan
  fixedStorage : ReadyImpliesNoFutureAllocationDemand serverProcessPlan
  socketGeneration : SocketIdentityAndGenerationInvariant serverProcessPlan
  listenerAuthority : ExactlyOneListenerAuthority serverProcessPlan
  admissionPermits : ActiveConnectionsCorrespondToPermits serverProcessPlan 4
  workerSlots : DisjointWorkerSlotOwnership serverProcessPlan
  receiveCancelRace : EveryReceiveLoanHasOneRaceWinner serverProcessPlan
  sendCancelRace : EverySendSuffixHasOneRaceWinner serverProcessPlan
  receiveFragments : PositiveReceivesAppendExactByteChunks serverProcessPlan
  sendPrefixes : PositiveSendsCommitExactPrefixes serverProcessPlan
  streamGeneration : StreamIdentityMonotonicAndNeverReused serverProcessPlan
  streamLifecycle : EveryFrameRespectsHttp2StreamState serverProcessPlan
  continuation : HeaderBlockContinuationIsConnectionExclusive serverProcessPlan
  hpackState : HpackContextsAreOrderedBoundedAndConnectionLocal serverProcessPlan
  hpackValidity : EveryAcceptedFieldSectionHasValidRfc7541Decoding serverProcessPlan
  hpackCancellationRouting : StreamCancellationNeverTargetsConnectionHpackState serverProcessPlan
  flowControl : ConnectionAndStreamCreditsConserved serverProcessPlan
  flowBackpressure : ExhaustedCreditPreventsDataAdmissionAndEmission serverProcessPlan
  controlProgress : ControlFramesNeverConsumeDataCredit serverProcessPlan
  frameCoverage : EveryRfc9113FrameKindHasDeclaredTransition serverProcessPlan
  errorScope : EveryProtocolErrorHasRfc9113Scope serverProcessPlan
  unknownExtensions : UnknownExtensionFramesAreIgnoredWithoutStateCorruption serverProcessPlan
  noPush : PushPromiseIsConnectionProtocolError serverProcessPlan
  deprecatedPriority : PrioritySignalsDoNotAffectBehavior serverProcessPlan
  settings : SettingsApplyAtomicallyBeforeAcknowledgement serverProcessPlan
  settingsWindowRebase : PeerInitialWindowRebasePreservesSignedCredit serverProcessPlan
  ping : PingAcknowledgementsPreserveExactOpaquePayload serverProcessPlan
  goaway : GoawayPreservesProcessedStreamPrefix serverProcessPlan
  outputOrder : ConnectionWriterSerializesFramesAndPreservesStreamOrder serverProcessPlan
  streamCancellation : EveryStuckStreamHasOneCancelRaceWinner serverProcessPlan
  shutdown : ShutdownPublicationAndCustodyInvariant serverProcessPlan
  obligations : ExactNetworkObligationPartition serverProcessPlan
  resources : ExactServerResourcePartition serverProcessPlan
```

Splitting these fields is a proof-economy choice. Replacing the fair output
scheduler should reprove output ordering and perhaps progress, not HPACK parsing
or socket generation. Raising the stream bound changes capacity/resource proofs
and fixed layout, not route correctness.

Cancellation is optional compositional metadata. It is not a field of
`ProcessCorrect`, and an ordinary serial function receives only the library's
weakest uncancellable summary. Rich cancellation appears here because this
server promises stream reset, graceful connection drain, and bounded shutdown.

The summary is built from the same structure as the realization:

```lean
def hpackSliceSummary :
    CancellationSummary (Hpack.decodeSliceProcess protocolProfile) :=
  CancellationSummary.uncancellableWorkingSlice
    (Hpack.decodeSliceCorrect protocolProfile)
    (.stepsAtMost Hpack.decodeSliceStepBound)
    hpackSliceStateProtocol

def hpackBetweenSlices :
    CancellationSummary (Hpack.betweenSlicesProcess protocolProfile) :=
  CancellationSummary.cancelPoint
    Hpack.betweenSlicesSafe
    Hpack.pendingCancellationCustody
    Hpack.cancelPreservesCommittedDecoderState

def hpackDecoderCancellation : CancellationSummary hpackDecoderProcess :=
  CancellationSummary.transport
    (Hpack.decoderDecomposesIntoSlices protocolProfile)
    (CancellationSummary.loop
      (CancellationSummary.seq hpackSliceSummary hpackBetweenSlices)
      Hpack.everyContinuingIterationConsumesInput
      Hpack.everyContinuingIterationCrossesCancelPoint)
```

One bounded HPACK slice is masked. Cancellation cannot observe a half-inserted
dynamic-table entry or partially advanced Huffman state. A request is retained
as an affine pending occurrence and consumed between slices, where the last
committed decoder state is exact. The loop theorem supplies bounded delay from
the slice step bound; a monolithic decoder with an unbounded masked loop would
fail this construction.

The selected Win32 plan has no provider cancellation operation. Its
nonblocking calls and bounded `WSAPoll`/`Sleep` calls are uncancellable segments
followed by real cancellation-observation blocks:

```lean
def receiveCancellation : CancellationSummary Http2.receiveByteSegment :=
  CancellationSummary.transport Http2.receiveByteSegmentDecomposition
    (CancellationSummary.seq receiveReadinessCall
      (CancellationSummary.seq receiveReadinessObservation
        (CancellationSummary.seq receiveCall receiveResultObservation)))

def partialSendCancellation : CancellationSummary Http2.partialSendSegment :=
  CancellationSummary.transport Http2.partialSendSegmentDecomposition
    (CancellationSummary.seq
      (CancellationSummary.loop partialSendIterationCancellation
        Http2.remainingSuffixDecreasesOrProviderFrontier
        Http2.everyContinuingPartialSendIterationReachesReadinessObservation)
      completedFrameCancelPoint)
```

`WSAPoll`, `recv`, and `send` quantify over completion, readiness timeout,
`WSAEWOULDBLOCK`, failure, and peer close. Cancellation is not attributed to
those APIs: the callback only publishes a request, and the subsequent displayed
observation block consumes or defers it. After a positive
`send(k)`, the prefix-commit segment is briefly uncancellable: it transfers
exactly the first `k` bytes to committed history and restores ownership of the
exact suffix. The writer then either continues its bounded partial-send loop or
reaches the completed-frame observation point. This prevents both duplicate
bytes and disappearing bytes.

No observation permits a stream reset to discard the middle of a frame. A
stream-scoped request is retained while the exact suffix finishes and can emit
RST_STREAM at the next frame boundary under writability, fairness and
connection-survival premises. If those premises fail, timeout/escalation closes
the connection with exact suffix disposition. If no byte was committed, the
whole unselected frame can be returned without a wire effect.

Flow-control wait is itself a cancellation point. No CPU work or socket call is
needed to reset a stream whose connection or stream window is zero. Cancelling
there returns only unselected DATA capacity; credit already debited for a
selected frame remains associated with that frame until send or connection
close.

```lean
def streamCancellation : CancellationSummary streamProcess :=
  CancellationSummary.transport Http2.streamProcessDecomposition
    (CancellationSummary.loop
      (CancellationSummary.choice
        (CancellationSummary.seq streamTransitionSummary
          flowCreditWaitCancellation)
        partialSendCancellation
        Http2.streamIterationBranchJoin)
      Http2.streamIterationProgress
      Http2.everyContinuingStreamIterationCrossesCancelPoint)

def connectionCancellation : CancellationSummary connectionProcess :=
  CancellationSummary.supervisor
    connectionLoopCancellation
    (CancellationSummary.parallel
      hpackDecoderCancellation connectionWriterCancellation streamCancellation
      Http2.connectionChildAddressedCancellation
      Http2.connectionChildJoinDisposition)
    Http2.goawayDrainSupervisorPolicy
    Http2.noForcedStopOutsideConnectionSafePoint

def rootShutdownCancelPoint :
    CancellationSummary (FixedPool.rootShutdownPoint processPolicy) :=
  CancellationSummary.cancelPoint
    FixedPool.rootShutdownSafe
    FixedPool.pendingShutdownCustody
    FixedPool.shutdownStopsAdmission

def rootServiceCancellation :
    CancellationSummary (FixedPool.serverRootProcess processPolicy) :=
  CancellationSummary.loop
    (CancellationSummary.seq
      rootShutdownCancelPoint
      (CancellationSummary.uncancellableCall
        Std.Win32.Sleep.correct
        (.providerReturnsWithin resourcePolicy.pollQuantum)))
    FixedPool.rootServiceIterationProgress
    FixedPool.everyRootIterationCrossesShutdownPoint

def serverCancellation : CancellationSummary memoryServerProcess :=
  CancellationSummary.transport FixedPool.memoryServerProcessDecomposition
    (CancellationSummary.supervisor
      rootServiceCancellation
      (CancellationSummary.parallelFamily workerAcceptCancellation)
      FixedPool.serverShutdownPolicy
      FixedPool.noForcedWorkerStopWithLiveCustody)

theorem serverCancellationExports :
    ∃ contract, serverCancellation.exportedContract = some contract :=
  CancellationSummary.supervisor_exports FixedPool.serverShutdownPolicy

theorem serverExportedContractCompatibleWithSupervisor :
    ExportedContractCompatibleWithSupervisor
      serverCancellation FixedPool.supervisorPolicy :=
  FixedPool.serverExportedContractCompatible
    serverCancellationExports

def serverTerminationFacet :
    TerminationFacet memoryServerCorrect
      (.supervised FixedPool.supervisorPolicy) :=
  CancellationSummary.toSupervisedTerminationFacet
    serverCancellation memoryServerCorrect FixedPool.supervisorPolicy
    serverCancellationExports serverExportedContractCompatibleWithSupervisor
```

Choice retains only guarantees valid for its reachable branches. Each fair
continuing loop crosses a real observation point or finishes a bounded provider
call and reaches one. Parallel
composition addresses cancellation to exact live incarnations and waits for
the required child dispositions. The connection supervisor turns stream
deadline cancellation into frame-finish-then-RST when its named premises hold,
or exact connection teardown when they do not; connection
cancellation freezes the accepted stream prefix, emits GOAWAY, drains or resets
children, settles the writer suffix and HPACK state, and only then closes the
socket. The server supervisor stops admission, cancels/drains connections,
joins workers, and reaches the normal or declared failed terminal boundary. It
cannot manufacture a safe forced stop in the middle of any child transition.
The root composes only its listener/service/shutdown loop with the worker
family. Connection policy is already inside each worker iteration, so it is not
re-applied or double-counted at the root.
`exportedContract` is optional: the combinators expose one only after proving
enough delay/progress and exact disposition facts. The separately named
compatibility proof shows that its causes, deadlines, escalation, and terminal
dispositions match the fixed-pool supervisor. `toSupervisedTerminationFacet` is
the bridge from the calculated summary to the opt-in promise consumed by the
plan; its `CancellationBackedContract` retains the summary and exactness witness
inside the facet rather than discarding them. Cooperative callers use the
distinct cooperative bridge. Nothing adds a field to `ProcessCorrect`.

The calculation is structural rather than a new monolithic server proof:

| constructor | local evidence | calculated result |
|---|---|---|
| uncancellable | ordinary correctness plus finite bound or named environment pending | request stays affine; no interior safe point |
| cancel point | typed state/custody and exact cancel disposition | consumes one pending request or continues unchanged |
| bounded uncancellable call | provider return bound and ordinary result custody | pending cancellation remains affine until the next observation |
| sequence | compatible boundary masks/custody | delay adds; safe-point sets compose |
| choice | exhaustive branch classifier | only guarantees common to every reachable branch |
| loop | per-iteration progress plus point/frontier coverage | finite delay or named environment pending on every fair cycle |
| parallel | addressed occurrences plus child join disposition | no sibling cancellation and exact aggregate settlement |
| supervisor | child summaries, shutdown order, deadline/escalation policy | exported contract only if no unsafe forced stop is needed |

The proof is induction over this expression. Each constructor preserves the
unique pending occurrence and terminal resource/obligation partition. Delay is
finite arithmetic for bounded masked segments and provider calls, maximum/join
for parallel children, and the supplied cycle
argument for loops. A missing branch, an unbounded masked cycle, or a terminal
path without disposition makes `exportedContract = none`; automation must report
that failed premise rather than synthesize a promise.

The algebra is associative at sequence boundaries, so refactoring or flattening
does not change the cancellation claim:

```lean
theorem cancellationSequenceRegroupingIsIrrelevant :
    CancellationSummary.seq a (CancellationSummary.seq b c) =
      CancellationSummary.transportProcessAssoc
        (CancellationSummary.seq (CancellationSummary.seq a b) c) :=
  CancellationSummary.seq_assoc _ _ _
```

```lean
theorem serverProcessPlanRealizes :
    ProcessPlanRealizes spec serverProcessPlan := by
  exact FixedPool.weaveCorrect
    serverComposition serverTerminationFacet
    memoryServerCorrect connectionCorrect streamCorrect
    hpackDecoderCorrect connectionWriterCorrect
    Std.Process.Network.allCorrect Std.Process.Clock.allCorrect
    Std.Process.Supervision.allCorrect Std.Process.Resource.closeHandleCorrect
    Std.Process.System.shutdownSignalCorrect
    Std.Process.Terminal.finishCorrect
```

The reusable weave theorem performs induction/coinduction over process
transitions. A child step uses its local preservation theorem; unrelated state
frames; a channel step checks its pre/post relation and transfers custody;
spawn/cancel checks generation authority; observations project to the precious
denotation. Infinite service is handled prefix-safely, while conditional
progress quantifies over fair scheduler/environment strategies.

## 5. Flow control and cancellation

For received DATA of flow-controlled length `n`, the transition requires both
`connectionReceiveCredit ≥ n` and `streamReceiveCredit ≥ n`, then debits both.
Releasing consumed body bytes may enqueue WINDOW_UPDATE and restores the
corresponding abstract capacity. Padding counts exactly as RFC 9113 requires.

For emitted DATA, selection requires both peer-advertised windows. Selection
reserves/debits credit before the frame enters the unique writer. A partial
`send(k)` commits exactly `k` bytes of the serialized frame; it does not restore
flow credit, because HTTP/2 credit accounts selected DATA payload, not syscall
completion. On cancellation, queued unselected data returns capacity; a
partially committed frame remains connection-owned until its suffix is sent or
the connection is closed.

Control frames consume control slots but never DATA window credit. Reserved
control capacity ensures SETTINGS ACK, PING ACK, RST_STREAM, WINDOW_UPDATE, and
GOAWAY are not blocked behind a full DATA queue. If the bounded control queue
itself would overflow because a hostile peer generates mandatory replies faster
than progress, the connection takes the declared `ENHANCE_YOUR_CALM`/resource
policy error path instead of allocating.

Each stream has an absolute progress deadline tied to `(connection generation,
stream id)`. Expiry races with the exact next stream transition and has one
winner. If no frame is partially committed, it enqueues RST_STREAM and returns
stream-local capacity without closing healthy siblings. With a partial frame,
the unconditional result is instead
`finishCurrentFrameThenRst ∨ connectionTeardownWithExactSuffixDisposition`.
The RST branch requires named writable-peer, writer-fairness, and
connection-survival premises; a peer which never accepts the suffix can force
the exact teardown branch. Connection-idle expiry and connection-scope faults
cancel all descendants.

`beginGracefulShutdown` carries an explicit `goawayPublished` state. Its first
successful call consumes one control slot and freezes the last-stream prefix;
later calls return `alreadyPublished`, consume no capacity and preserve that
prefix. The caller checks the queue-failure result and takes exact connection
teardown. Under drain premises the connection closes after settling children;
deadline expiry takes the separately proved suffix/obligation escalation.
Shutdown then joins workers, unregisters the handler, ends Winsock, and exits
zero unless cleanup failed.

HPACK cancellation quantifies distinct `committed` and private `working` states.
A request arriving during a bounded slice either returns exactly `committed`, or
the slice finishes through its atomic commit relation and returns a separately
named committed successor. No theorem treats an arbitrary mid-table mutation as
a committed decoder state.

## 6. Concrete resource theorems

```lean
theorem streamMemoryBound (connection) (stream) :
    EveryExecutionUsesAtMost
      (streamScope connection stream)
      ServerResourceMetric.grassOwnedResidentBytes
      (Http2.streamBytes processPolicy)

theorem connectionMemoryBound (id) :
    EveryExecutionUsesAtMost
      (connectionScope id)
      ServerResourceMetric.grassOwnedResidentBytes
      (Http2.connectionBytes processPolicy)

theorem connectionStreamBound (id) :
    EveryReachableStateSatisfies
      (ActiveStreams id ≤ resourcePolicy.maxConcurrentStreamsPerConnection)

theorem serverSocketBound :
    EveryExecutionUsesAtMost ProcessScope.root
      ServerResourceMetric.socketDescriptors 5

theorem serverHandleBound :
    EveryExecutionUsesAtMost ProcessScope.root
      ServerResourceMetric.windowsHandles
      (ServerResourceBudget.handles processPolicy)

theorem serverRootResidentMemoryBound :
    EveryExecutionUsesAtMost ProcessScope.root
      ServerResourceMetric.grassOwnedResidentBytes
      (ServerResourceBudget.residentBytes resourcePolicy)

theorem serverRootResourceEquation :
    ExactRootResourceEquation serverProcessPlan serverResourceAxisRealization
      (ServerResourceBudget.allAxes resourcePolicy)
```

These are gross subgraph bounds, including descendants and boundary escrow;
they do not use unjustified subtraction in an arbitrary resource algebra.
Stratified resource models can add data-center or microcontroller axes without
changing the server behavior model.

## 7. Win10 x64 projection and provider plan

```lean
def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10Http2PriorKnowledge
    (endpoint := .ipv4Loopback 8080)
    (gracefulShutdownStatus := 0)
    (startupFailureStatus := 1)

def platformPlan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64Http2FixedPool projection
```

The plan selects Winsock 2.2 nonblocking sockets, `WSAPoll`, `CreateThread`, a
console-control callback, `GetTickCount64`, x64 ABI, COFF/PE32+, and ASLR. The
portable deadline is related to the selected monotonic provider, including
wrap/return behavior. The import set is derived from the closed source and has
no allocation API.

Positive `recv` and `send` results are adversarial values bounded only by the
requested count. `WSAEWOULDBLOCK`, orderly close, other errors, poll timeout,
readiness, callback timing, thread scheduling, and handle/socket reuse all enter
the universally quantified provider model. API documentation anchors the model;
fuzzers and boundary probes compare physical behavior to it.

## 8. Static source closure

`Data.lean` derives the client preface, SETTINGS frame, literal-without-indexing
response blocks, route bytes, generated HPACK tables, bind address, and all
fixed state sizes. It proves the SETTINGS and response HPACK round trips. The
static writable region contains exactly four worker slots, four connection
states, and `4 × 128` stream slots.

The import table is limited to:

```text
KERNEL32: CreateThread ResumeThread WaitForSingleObject CloseHandle Sleep
          SetConsoleCtrlHandler GetTickCount64 ExitProcess
WS2_32:   WSAStartup WSASocketW bind listen ioctlsocket WSAPoll accept recv send
          WSAGetLastError closesocket WSACleanup
```

No post-ready allocation is possible because no allocator is in the source
closure. The PE still contains normal relocations, unwind metadata, import/IAT
data, NX permissions, writable data permissions, and ASLR-compatible abstract
RIP references.

## 9. First-class assembly

The complete comment-free author fixture is
[`Spikes/4_Web_Server/Assembly.lean`](../Spikes/4_Web_Server/Assembly.lean).
Its visible labels include:

```text
entry -> create_workers -> resume_workers -> publish_ready -> service_loop
startup_partial_workers -> resume_failure_workers -> join_workers
worker_entry -> worker_gate -> accept_wait -> preface_loop
connection_schedule -> receive_frames -> frame_parse_loop
frame_headers/continuation/data/settings/ping/goaway/rst/window/priority/unknown
decode_fields -> enqueue_success/not_found
send_selected_frame -> send_suffix_loop
stream_error or connection_error -> draining -> close -> accept_wait
join_workers -> close_listener -> cleanup_wsa -> ExitProcess
```

The setup, calls, branches, register choices, atomic words, partial-send syscall
loop, join/cleanup, and error dispatch are authored assembly. Complex parsing,
HPACK, state-transition, scheduling, and bounded-ring operations are local typed
fragment constructors. `Macros.lean` carries every constructor body as an
assembly algorithm, its exact raw expansion, references, citations, and machine
certificate. The macro-shaped names in the listing are only transparent adapters
to those constructors; no absent standard-library implementation is the body.
This is not an opaque compiler escape: an assembly author can replace any call
with novel raw instructions and prove the same local entry/exit contract.

The constructor hierarchy includes client-preface consumption, bounded receive ring,
frame-header parsing/dispatch, CONTINUATION assembly, full HPACK decode, request
field validation, SETTINGS/WINDOW_UPDATE/RST/GOAWAY/PING transitions, stream
state, connection/stream credit debit, bounded control/response enqueue, fair
selection, frame serialization, partial-prefix commit, deadline cancellation,
and state release. HPACK is further split into integer, string, Huffman, and
field-section constructors with committed/working state explicit. A missing
algorithm cannot be replaced by an unexplained Hoare assertion or a reference
to a future `Grass.Std` module. These local bodies are the proposed standard
library implementations and may later move without changing their contracts.

```lean
def serverSourceClosure : ClosedAsmSource platformPlan :=
  ClosedAsmSource.closeWithFragmentHierarchy
    serverSource serverMacros serverFragmentHierarchy
    serverStaticObjects serverImports

theorem serverSourceClosureComplete : SourceClosureComplete serverSourceClosure := by
  validate_source_closure

def serverExpandedSource : RawAsmSource platformPlan :=
  serverSourceClosure.expand

theorem serverExpansionExact :
    SourceElaboratesExactlyTo serverSourceClosure serverExpandedSource := by
  exact ClosedAsmSource.hierarchicalExpansionExact
    serverSourceClosure serverFragmentExpansionExact
```

The closure records exact macro definitions, static objects, imports,
relocations, and expanded raw listing. Ghost instructions are erased only by the
proved expansion; the layer accepted by encoding contains raw instructions.

## 10. Assembly-to-model bindings

```lean
theorem sourceImplementsDriver :
    AssemblyImplements
      (ProcessRealization.explicit serverProcessPlanRealizes)
      platformPlan serverExpandedSource := by
  verify_asm

theorem sourceImplementsHttp2Model :
    AssemblyRefinesStateMachine serverExpandedSource connectionModel := by
  exact sourceImplementsDriver.http2ConnectionRefinement

theorem sourcePreservesFlowCredit :
    AssemblyPreservesInvariant serverExpandedSource
      (Http2.ConnectionAndStreamFlowCreditInvariant connectionModel) := by
  exact sourceImplementsHttp2Model.preserve flowCreditsConserved

theorem sourceRespectsFixedStorage :
    AssemblyNeverAllocatesAfterReady serverExpandedSource resourcePolicy := by
  verify_asm_resource_calls

def serverCancellationBlockMap :
    CancellationCfgMap serverExpandedSource serverCancellation :=
  cancellation_cfg_total {
    service_loop => observe FixedPool.CancelPoint.rootShutdownObservation
    worker_gate => observe FixedPool.CancelPoint.workerGateObservation
    accept_wait => observe FixedPool.CancelPoint.acceptLoopObservation
    preface_loop => observe Http2.CancelPoint.prefaceObservation
    connection_schedule => observe Http2.CancelPoint.schedulerObservation
    receive_frames => uncancellable Http2.Segment.boundedReceive
    receive_result_observation => observe Http2.CancelPoint.receiveResultObservation
    frame_parse_loop => safeState Http2.SafePoint.frameBoundary
    decode_fields => expands hpackDecoderCancellation
    send_selected_frame => uncancellable Http2.Segment.selectDebitSerialize
    send_suffix_loop => uncancellable Http2.Segment.boundedWritablePoll
    send_readiness_observation => observe Http2.CancelPoint.writerReadinessObservation
    send_positive => uncancellable Http2.Segment.commitSentPrefix
    connection_draining => safeState Http2.SafePoint.drainBoundary
    connection_close => uncancellable Http2.Segment.closeAndReleaseConnection
    connection_closed_boundary => observe Http2.CancelPoint.connectionClosedObservation
    console_handler => requestPublisher FixedPool.CancellationSource.consoleControl
    worker_return => terminal FixedPool.Terminal.workerDischarged
    finish_status => terminalChoice
      FixedPool.Terminal.normalDischarged
      FixedPool.Terminal.failedAdoption
    fatal_exit => terminal FixedPool.Terminal.failedAdoption
    edges => classifyEveryExpandedEdgeByInstructionSemantics
  }

theorem serverCfgCancellationRefines :
    CancellationCfgRefines
      serverExpandedSource serverCancellationBlockMap serverCancellation := by
  verify_cancellation_cfg

theorem everyExpandedBlockAndEdgeIsClassified :
    TotalCancellationCfgClassification
      serverExpandedSource serverCancellationBlockMap :=
  serverCfgCancellationRefines.total
```

Straight-line instruction verification should symbolically execute and close
routine register/flag/memory facts. Macro contracts summarize established raw
instruction bodies. Block entry types name registers, stack shape, regions,
loans, credits, ghost protocol state, and obligations; each exit is checked
locally, and every jump/call proves its target entry contract. Novel assembly is
therefore possible without forcing the author to restate the global server
proof.

The comment-free fixture lists every expanded label, including setup, callback,
success/failure unwind, cleanup, no-return and all frame/error blocks; every
expanded edge is classified by its exact instruction semantics. A `safeState`
only establishes custody/invariant shape. An `observe` block additionally loads
or consumes the pending request and branches to its continuation/disposition.
Callback arrival may latch a request but cannot jump to a safe state or pretend
an interior instruction observed it. Fault edges retain their separately typed
failed disposition, and the totality theorem rejects every reachable unmapped
block.

Positive fixtures include cancellation at a zero-window wait, a bounded
readiness return followed by actual observation, conditional per-stream
RST_STREAM or exact teardown, GOAWAY/drain,
HPACK cancellation between slices, partial-send cancellation after exact prefix
commit, and normal/failed terminal settlement. Negative fixtures require proofs
of impossibility:

```lean
theorem noCancellationInsideHpackMutation :
    ¬ CancellationSafePoint hpackDecoderCancellation
      Hpack.ControlPoint.midDynamicTableMutation

theorem noCancellationBeforeSentPrefixCommit :
    ¬ CancellationSafePoint partialSendCancellation
      Http2.ControlPoint.sendReturnedBeforePrefixCommit

theorem noForcedWorkerStopWithLiveSocket :
    ¬ PermittedForcedCancellation serverCancellation
      FixedPool.ControlPoint.workerOwnsLiveSocket

theorem uncancellableInfiniteCallCannotClaimBoundedCancellation
    (call : ProcessSpec) (correct : ProcessCorrect call)
    (forever : MayBlockForeverWithoutEnvironmentFrontier call) :
    (CancellationSummary.uncancellable correct .environmentPending).exportedContract =
      none
```

An ordinary registered serial function has exactly
`CancellationSummary.weakestUncancellable function.correct`; it supplies no
cancelpoint, supervisor, or richer proof.

## 11. Verified program and exact PE bytes

```lean
def serverVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    using explicit_process serverProcessPlanRealizes
    using_cancellation serverCancellation
    with serverSource

def bytes : ByteArray := emitProgram serverVerified

def artifact : PE32Plus := serverVerified.linkedArtifact

theorem writerRoundTrip :
    PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem parserConforms (input : ByteArray) :
    PE32Plus.parse input = .error ∨
    ∃ image, PE32Plus.parse input = .ok image ∧
      PE32Plus.ConformsToSpecification input image :=
  PE32Plus.parserConforms input

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact serverVerified.rawProgram :=
  serverVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact := rfl

theorem admissibleLoadsRefineHttp2 :
    ∀ load ∈ PE32Plus.admissibleLoads bytes,
      LoadedExecutionRefines load spec :=
  serverVerified.artifactCorrectness.everyAdmissibleLoad
```

The serializer round trip is not the executable theorem. Exact instruction
encode/decode laws, relocations, loader assumptions, imports, ABI, memory
permissions, and artifact layout are composed to show that every admitted load
of these exact bytes executes the verified raw program and refines the spec.

## 12. Failure matrix

| Failure or event | Required local action | Scope | Observable/terminal effect |
|---|---|---|---|
| startup/worker creation before ready | unwind acquired handles/socket/Winsock | program | no HTTP bytes; exit nonzero |
| invalid client preface | close or GOAWAY when legal | connection | connection failure only |
| malformed frame length/flags/stream id | RFC error code | RFC-selected stream/connection | siblings preserved for stream error |
| HPACK invalid index/Huffman/table update | COMPRESSION_ERROR | connection | cancel descendants, GOAWAY/close |
| stream-state violation | RFC-selected code | stream or connection | exact scoped transition |
| receive window exhausted | FLOW_CONTROL_ERROR | stream or connection | no uncredited DATA admitted |
| send windows zero | retain queued DATA and wait | stream/connection backpressure | control/sibling progress allowed |
| control queue policy exceeded | bounded overload error | connection | no allocation attempt |
| per-stream deadline | finish current frame then RST, or exact connection teardown | stream/connection | siblings continue only on RST branch |
| peer RST_STREAM | discard/return stream-local queued custody | stream | exact reset observation |
| peer GOAWAY | stop affected new work, drain prefix | connection | prefix semantics |
| peer orderly close or recv/send failure | reclaim all connection descendants | connection | explicit connection outcome |
| shutdown | stop admission, GOAWAY, settle/cancel, join | server | exit 0 unless cleanup fails |
| irrecoverable join/cleanup failure | adopt process-owned obligations | program | exit nonzero |

Nothing says prior successful observations become false after failure. Failure
changes which continuation is required. Program exit may adopt operating-system
cleanup obligations under the platform rule; it may not silently adopt an
external protocol obligation that the spec requires to remain observable.

## 13. Change locality

| Change | Precious proof | Local/model proof | Assembly/artifact |
|---|---|---|---|
| response body bytes | route theorem recomputes | response lengths/HPACK block | rodata and affected encoding |
| add route | route correctness | field validation/selection | route table, local dispatch |
| 128 -> 256 streams | resource-selected spec instance | capacity and layout bounds | fixed storage/layout |
| four -> eight workers with same admission | none | realization population/synchronization | setup, slots, PE data |
| scheduler algorithm | none if boundary preserved | order/fairness and local refinement | writer assembly |
| custom HPACK assembly | none | decoder refinement only | macro replacement/listing |
| WSAPoll -> IOCP | none | provider/process realization | connection driver/imports |
| Win32 -> Unix | none | projection/provider/resource axes | ABI/ISA/artifact |
| add TLS | behavior/profile changes | TLS process/resource/refinement | crypto/network/artifact |

“Sibling proof reuse” is conditional on unchanged exported channel and resource
boundaries. The corpus must measure elaboration/cache invalidation rather than
calling it O(1) by assertion.

## 14. Review questions

1. Is the precious HTTP/2 profile the minimum shippable behavior, or are encoder
   choices and unknown-route policy too concrete?
2. Are logical stream processes worth their ceremony for causal attribution,
   flow-control proofs, and isolated cancellation?
3. Does connection-local HPACK ordering compose cleanly with independent stream
   progress, or is another serialization boundary needed?
4. Do the capacity tokens make every memory bound and backpressure transition
   constructive, including control frames and queued partial writes?
5. Is the stream deadline a defensible product policy, and is reset without
   sibling cancellation the correct outcome?
6. Are transparent macros at the right granularity for readable authored
   assembly and local replacement?
7. Does every claimed frame/error case have a visible transition and adversarial
   fixture, especially CONTINUATION, PUSH_PROMISE, and unknown extensions?
8. Does the exact artifact chain retain enough source closure to reproduce and
   inspect every expanded instruction byte?

## 15. Comment-free expected source

The expected author-owned modules are:

```text
Spikes/4_Web_Server/
  Spec.lean
  Process.lean
  Cancellation.lean
  Macros.lean
  Assembly.lean
  Program.lean
```

They intentionally contain no explanatory comments, `sorry`, `admit`, `axiom`,
`unsafe`, or decision-by-execution proof. This document owns the rationale and
proof commentary; the fixtures expose exactly the declarations and proof terms
the eventual libraries should let an author maintain.


## Exact authored source snapshot

This section is the author-maintained Lean surface defined by
[SPIKE_AUTHORING.md](SPIKE_AUTHORING.md). Earlier code blocks in this document
are generated expansions, library interface sketches, or proof sketches unless
they are explicitly labeled authored source. Reviewers must compare this
snapshot with `Spikes/4_Web_Server/` exactly.

### `Assembly.lean`

```lean
import Grass.Assembly.X86
import Spikes.«4_Web_Server».Macros

namespace Grass.Spikes.WebServer

structure ServerEntryFrameFields where
  shadow : Bytes 32
  callArg5 : UInt64
  callArg6 : UInt64
  locals : Bytes 8

def ServerEntryFrame : FrameLayout Win64 :=
  FrameLayout.derive ServerEntryFrameFields

structure WorkerFrameFields where
  shadow : Bytes 32
  locals : Bytes 24

def WorkerFrame : FrameLayout Win64 := FrameLayout.derive WorkerFrameFields

def serverSource : AsmSource platformPlan := asm_source {

entry: @entrypoint @unwind(server_entry_unwind)
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, ServerEntryFrame.size
    xor  ebp, ebp
    xor  r13d, r13d
    mov  qword ptr [rip+listen_socket], INVALID_SOCKET
    mov  dword ptr [rip+shutdown], 0
    mov  dword ptr [rip+fatal], 0
    mov  dword ptr [rip+start_gate], 0
    mov  ecx, 0x0202
    lea  rdx, [rip+wsa_data]
    call qword ptr [rip+__imp_WSAStartup]
    test eax, eax
    jnz  exit_failure_no_wsa
    mov  ecx, AF_INET
    mov  edx, SOCK_STREAM
    mov  r8d, IPPROTO_TCP
    xor  r9d, r9d
    mov  qword ptr [rsp + ServerEntryFrame.callArg5], 0
    mov  dword ptr [rsp + ServerEntryFrame.callArg6], 0
    call qword ptr [rip+__imp_WSASocketW]
    cmp  rax, INVALID_SOCKET
    je   startup_failure_wsa
    mov  r12, rax
    mov  qword ptr [rip+listen_socket], rax
    mov  rcx, r12
    lea  rdx, [rip+bind_address]
    mov  r8d, 16
    call qword ptr [rip+__imp_bind]
    test eax, eax
    jnz  startup_failure_socket
    mov  rcx, r12
    mov  edx, SOMAXCONN
    call qword ptr [rip+__imp_listen]
    test eax, eax
    jnz  startup_failure_socket
    mov  dword ptr [rip+nonblocking_one], 1
    mov  rcx, r12
    mov  edx, FIONBIO
    lea  r8, [rip+nonblocking_one]
    call qword ptr [rip+__imp_ioctlsocket]
    test eax, eax
    jnz  startup_failure_socket
    lea  rcx, [rip+console_handler]
    mov  edx, 1
    call qword ptr [rip+__imp_SetConsoleCtrlHandler]
    test eax, eax
    jz   startup_failure_socket

create_workers: @placement [created := r13]
                @invariant created_prefix(worker_handles, worker_slots)
                @measure executionEnvelope.workerCount-r13
    cmp  r13d, executionEnvelope.workerCount
    je   resume_workers
    mov  rax, r13
    imul rax, rax, WORKER_SLOT_BYTES
    lea  r9, [rip+worker_slots]
    add  r9, rax
    xor  ecx, ecx
    xor  edx, edx
    lea  r8, [rip+worker_entry]
    mov  dword ptr [rsp + ServerEntryFrame.callArg5], CREATE_SUSPENDED
    mov  qword ptr [rsp + ServerEntryFrame.callArg6], 0
    call qword ptr [rip+__imp_CreateThread]
    test rax, rax
    jz   startup_partial_workers
    lea  rdx, [rip+worker_handles]
    mov  qword ptr [rdx+r13*8], rax
    inc  r13d
    jmp  create_workers

resume_workers:
    xor  r14d, r14d
resume_loop: @placement [resumed := r14, created := r13]
             @invariant resumed_prefix @measure created-resumed
    cmp  r14d, r13d
    je   publish_ready
    lea  rdx, [rip+worker_handles]
    mov  rcx, qword ptr [rdx+r14*8]
    call qword ptr [rip+__imp_ResumeThread]
    cmp  eax, -1
    je   fatal_exit
    inc  r14d
    jmp  resume_loop

publish_ready:
    mov  eax, 1
    xchg dword ptr [rip+start_gate], eax
service_loop: @reactive_frontier bounded_sleep
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  join_workers
    mov  ecx, POLL_QUANTUM_MS
    call qword ptr [rip+__imp_Sleep]
    jmp  service_loop

startup_partial_workers:
    mov  ebp, 1
    mov  eax, 1
    xchg dword ptr [rip+shutdown], eax
    xor  r14d, r14d
resume_failure_workers: @placement [resumed := r14, created := r13]
                        @invariant failure_resumed_prefix
                        @measure created-resumed
    cmp  r14d, r13d
    je   join_workers
    lea  rdx, [rip+worker_handles]
    mov  rcx, qword ptr [rdx+r14*8]
    call qword ptr [rip+__imp_ResumeThread]
    cmp  eax, -1
    je   fatal_exit
    inc  r14d
    jmp  resume_failure_workers

join_workers: @placement [remainingWorkers := r13]
              @invariant joined_suffix(worker_handles) @measure remainingWorkers
    test r13d, r13d
    jz   unregister_handler
    dec  r13d
    lea  rdx, [rip+worker_handles]
    mov  rcx, qword ptr [rdx+r13*8]
    mov  edx, INFINITE
    call qword ptr [rip+__imp_WaitForSingleObject]
    cmp  eax, WAIT_FAILED
    je   fatal_exit
    lea  rdx, [rip+worker_handles]
    mov  rcx, qword ptr [rdx+r13*8]
    call qword ptr [rip+__imp_CloseHandle]
    test eax, eax
    jnz  join_workers
    mov  ebp, 1
    jmp  join_workers

unregister_handler:
    lea  rcx, [rip+console_handler]
    xor  edx, edx
    call qword ptr [rip+__imp_SetConsoleCtrlHandler]
    test eax, eax
    jnz  close_listener
    mov  ebp, 1

close_listener:
    mov  rcx, r12
    call qword ptr [rip+__imp_closesocket]
    test eax, eax
    jz   cleanup_wsa
    mov  ebp, 1
cleanup_wsa:
    call qword ptr [rip+__imp_WSACleanup]
    test eax, eax
    jz   finish_status
    mov  ebp, 1
finish_status:
    mov  eax, dword ptr [rip+fatal] @atomic(.acquire)
    or   ebp, eax
    mov  ecx, ebp
    call qword ptr [rip+__imp_ExitProcess]
    ud2 @unreachable_after_noreturn

startup_failure_socket:
    mov  rcx, r12
    call qword ptr [rip+__imp_closesocket]
startup_failure_wsa:
    call qword ptr [rip+__imp_WSACleanup]
exit_failure_no_wsa:
    mov  ecx, 1
    call qword ptr [rip+__imp_ExitProcess]
    ud2 @unreachable_after_noreturn
fatal_exit:
    mov  ecx, 1
    call qword ptr [rip+__imp_ExitProcess]
    ud2 @unreachable_after_noreturn

console_handler: @callback_leaf @atomic_only
    mov  eax, 1
    xchg dword ptr [rip+shutdown], eax
    mov  eax, 1
    ret

worker_entry: @thread_entry @unwind(worker_entry_unwind)
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, WorkerFrame.size
    mov  rbx, rcx
    mov  rsi, INVALID_SOCKET

worker_gate: @reactive_frontier initialization_gate
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  worker_return
    mov  eax, dword ptr [rip+start_gate] @atomic(.acquire)
    test eax, eax
    jnz  accept_wait
    mov  ecx, 1
    call qword ptr [rip+__imp_Sleep]
    jmp  worker_gate

accept_wait: @placement [workerSlot := rbx]
             @reactive_frontier poll_listener @invariant owns_worker_slot
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  worker_return
    mov  rax, qword ptr [rip+listen_socket]
    mov  qword ptr [rbx+POLL_SOCKET], rax
    mov  word ptr [rbx+POLL_EVENTS], POLLRDNORM
    mov  rcx, rbx
    mov  edx, 1
    mov  r8d, POLL_QUANTUM_MS
    call qword ptr [rip+__imp_WSAPoll]
    test eax, eax
    jle  accept_wait
    mov  rcx, qword ptr [rip+listen_socket]
    xor  edx, edx
    xor  r8d, r8d
    call qword ptr [rip+__imp_accept]
    cmp  rax, INVALID_SOCKET
    jne  accepted_connection
    call qword ptr [rip+__imp_WSAGetLastError]
    cmp  eax, WSAEWOULDBLOCK
    je   accept_wait
    mov  ecx, POLL_QUANTUM_MS
    call qword ptr [rip+__imp_Sleep]
    jmp  accept_wait
accepted_connection:
    mov  rsi, rax
    mov  rcx, rsi
    mov  edx, FIONBIO
    lea  r8, [rip+nonblocking_one]
    call qword ptr [rip+__imp_ioctlsocket]
    test eax, eax
    jnz  accepted_mode_failure
    mov  rcx, rbx
    mov  rdx, rsi
    call h2_initialize_connection_state
    call qword ptr [rip+__imp_GetTickCount64]
    mov  qword ptr [rbx+LAST_PROGRESS], rax
    jmp  preface_loop

accepted_mode_failure:
    mov  rcx, rsi
    call qword ptr [rip+__imp_closesocket]
    mov  rsi, INVALID_SOCKET
    jmp  accept_wait

preface_loop: @frontier_or_measure(preface_input_or_24-preface_count)
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  connection_shutdown
    call receive_into_ring
    cmp  eax, IO_PENDING
    je   connection_schedule
    cmp  eax, IO_CLOSED
    je   connection_peer_close
    cmp  eax, IO_FAILED
    je   connection_io_error
    mov  rcx, rbx
    call h2_consume_preface
    cmp  eax, PARSE_NEED_MORE
    je   preface_loop
    cmp  eax, PARSE_ERROR
    je   connection_protocol_error
    mov  rcx, rbx
    lea  rdx, [rip+settings_frame]
    mov  r8d, $settingsFrame.length
    call h2_enqueue_control
    test eax, eax
    jnz  connection_internal_error
    jmp  connection_schedule

connection_schedule: @reactive_frontier socket_readiness_or_deadline
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jz   connection_deadlines
    mov  rcx, rbx
    mov  edx, NO_ERROR
    call h2_enqueue_goaway
    cmp  eax, GOAWAY_QUEUE_FAILURE
    je   connection_goaway_failure
connection_deadlines:
    call qword ptr [rip+__imp_GetTickCount64]
    mov  rdx, rax
    mov  rcx, rbx
    call h2_check_connection_deadline
    test eax, eax
    jnz  connection_shutdown
    mov  rcx, rbx
    call h2_cancel_expired_streams
    mov  rcx, rbx
    call h2_release_closed_streams
    mov  rcx, rbx
    call h2_should_close_drained
    test eax, eax
    jnz  connection_close
    mov  rcx, rbx
    call h2_has_sendable_outbound
    test eax, eax
    jnz  send_selected_frame
    mov  rcx, rbx
    call connection_poll
    test eax, POLL_READABLE
    jnz  receive_frames
    test eax, POLL_WRITABLE
    jnz  send_selected_frame
    test eax, POLL_FAILED
    jnz  connection_io_error
    jmp  connection_schedule

receive_frames:
    call receive_into_ring
    cmp  eax, IO_PENDING
    je   connection_schedule
    cmp  eax, IO_CLOSED
    je   connection_peer_close
    cmp  eax, IO_FAILED
    je   connection_io_error

receive_result_observation: @cancellation_observation connection_receive_result
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jnz  connection_shutdown

frame_parse_loop: @measure buffered_complete_frames_or_need_input
    mov  rcx, rbx
    call h2_parse_frame_header
    cmp  eax, PARSE_NEED_MORE
    je   connection_schedule
    cmp  eax, PARSE_CONNECTION_ERROR
    je   connection_protocol_error
    mov  rcx, rbx
    call h2_require_initial_settings
    test eax, eax
    jnz  connection_protocol_error
    mov  rcx, rbx
    call h2_dispatch_frame
    cmp  eax, FRAME_DATA
    je   frame_data
    cmp  eax, FRAME_HEADERS
    je   frame_headers
    cmp  eax, FRAME_CONTINUATION
    je   frame_continuation
    cmp  eax, FRAME_SETTINGS
    je   frame_settings
    cmp  eax, FRAME_PING
    je   frame_ping
    cmp  eax, FRAME_GOAWAY
    je   frame_goaway
    cmp  eax, FRAME_RST_STREAM
    je   frame_rst_stream
    cmp  eax, FRAME_WINDOW_UPDATE
    je   frame_window_update
    cmp  eax, FRAME_PRIORITY
    je   frame_ignore_priority
    cmp  eax, FRAME_PUSH_PROMISE
    je   connection_protocol_error
    cmp  eax, FRAME_UNKNOWN
    je   frame_ignore_unknown
    jmp  connection_protocol_error

frame_headers:
    mov  rcx, rbx
    call h2_transition_stream
    cmp  eax, TRANSITION_STREAM_ERROR
    je   stream_protocol_error
    cmp  eax, TRANSITION_CONNECTION_ERROR
    je   connection_protocol_error
    test dword ptr [rbx+CURRENT_FLAGS], FLAG_END_HEADERS
    jz   begin_continuation
    jmp  decode_fields

begin_continuation:
    mov  rcx, rbx
    call h2_begin_header_block
    test eax, eax
    jnz  connection_protocol_error
    jmp  frame_parse_loop

frame_continuation:
    mov  rcx, rbx
    call h2_append_continuation
    test eax, eax
    jnz  connection_protocol_error
    test dword ptr [rbx+CURRENT_FLAGS], FLAG_END_HEADERS
    jz   frame_parse_loop

decode_fields:
    mov  rcx, rbx
    call hpack_decode_field_section
    cmp  eax, HPACK_CONNECTION_ERROR
    je   connection_compression_error
    mov  rcx, rbx
    call h2_validate_request_fields
    cmp  eax, REQUEST_OK
    je   enqueue_success
    cmp  eax, REQUEST_NOT_FOUND
    je   enqueue_not_found
    cmp  eax, REQUEST_STREAM_ERROR
    je   stream_protocol_error
    jmp  connection_protocol_error

enqueue_success:
    mov  rcx, rbx
    call h2_enqueue_response
    test eax, eax
    jnz  stream_refused
    jmp  frame_parse_loop

enqueue_not_found:
    mov  rcx, rbx
    call h2_enqueue_not_found
    test eax, eax
    jnz  stream_refused
    jmp  frame_parse_loop

frame_data:
    mov  rcx, rbx
    call h2_transition_stream
    cmp  eax, TRANSITION_STREAM_ERROR
    je   stream_protocol_error
    cmp  eax, TRANSITION_CONNECTION_ERROR
    je   connection_protocol_error
    mov  rcx, rbx
    call h2_debit_inbound_credit
    cmp  eax, FLOW_STREAM_ERROR
    je   stream_flow_error
    cmp  eax, FLOW_CONNECTION_ERROR
    je   connection_flow_error
    mov  rcx, rbx
    call h2_release_inbound_data
    test eax, eax
    jnz  connection_internal_error
    jmp  frame_parse_loop

frame_settings:
    mov  rcx, rbx
    call h2_apply_settings
    test eax, eax
    jnz  connection_protocol_error
    test dword ptr [rbx+CURRENT_FLAGS], FLAG_ACK
    jnz  frame_parse_loop
    mov  rcx, rbx
    mov  edx, CONTROL_SETTINGS_ACK
    call h2_enqueue_control
    test eax, eax
    jnz  connection_internal_error
    jmp  frame_parse_loop

frame_ping:
    mov  rcx, rbx
    call h2_ack_ping
    test eax, eax
    jnz  connection_protocol_error
    jmp  frame_parse_loop

frame_goaway:
    mov  rcx, rbx
    call h2_apply_goaway
    jmp  connection_draining

frame_rst_stream:
    mov  rcx, rbx
    call h2_apply_rst_stream
    test eax, eax
    jnz  connection_protocol_error
    jmp  frame_parse_loop

frame_window_update:
    mov  rcx, rbx
    call h2_apply_window_update
    cmp  eax, FLOW_STREAM_ERROR
    je   stream_flow_error
    cmp  eax, FLOW_CONNECTION_ERROR
    je   connection_flow_error
    jmp  frame_parse_loop

frame_ignore_priority:
    mov  rcx, rbx
    call h2_validate_ignored_priority
    test eax, eax
    jnz  connection_protocol_error
    jmp  frame_parse_loop

frame_ignore_unknown:
    mov  rcx, rbx
    call h2_consume_unknown_payload
    jmp  frame_parse_loop

send_selected_frame:
    mov  eax, dword ptr [rbx+TX_COMMITTED]
    cmp  eax, dword ptr [rbx+TX_LENGTH]
    jb   send_suffix_loop
    mov  rcx, rbx
    call h2_select_outbound
    test eax, eax
    jz   connection_schedule
    mov  rcx, rbx
    call h2_debit_outbound_credit
    cmp  eax, FLOW_BLOCKED
    je   connection_schedule
    cmp  eax, FLOW_ERROR
    je   connection_flow_error
    mov  rcx, rbx
    call h2_serialize_selected_frame
    test eax, eax
    jnz  connection_internal_error

send_suffix_loop: @frontier_or_measure(socket_writable_or_tx_length-tx_committed)
    mov  rcx, rbx
    call poll_connection_writable
    test eax, POLL_FAILED
    jnz  connection_io_error
    test eax, POLL_WRITABLE
    jz   connection_schedule
send_readiness_observation: @cancellation_observation writer_readiness_result
    mov  rcx, rbx
    call h2_observe_writer_cancellation
    cmp  eax, WRITER_CANCEL_CONNECTION_CLOSE
    je   connection_goaway_failure
    mov  rcx, rsi
    lea  rdx, [rbx+TX_BUFFER]
    add  rdx, qword ptr [rbx+TX_COMMITTED]
    mov  r8d, dword ptr [rbx+TX_LENGTH]
    sub  r8d, dword ptr [rbx+TX_COMMITTED]
    xor  r9d, r9d
    call qword ptr [rip+__imp_send]
    cmp  eax, SOCKET_ERROR
    jne  send_positive
    call qword ptr [rip+__imp_WSAGetLastError]
    cmp  eax, WSAEWOULDBLOCK
    je   connection_schedule
    jmp  connection_io_error
send_positive:
    test eax, eax
    jz   connection_io_error
    mov  rcx, rbx
    mov  edx, eax
    call h2_commit_sent_prefix
    cmp  dword ptr [rbx+TX_COMMITTED], dword ptr [rbx+TX_LENGTH]
    jne  send_suffix_loop
    jmp  connection_schedule

stream_refused:
    mov  edx, REFUSED_STREAM
    jmp  enqueue_stream_error
stream_protocol_error:
    mov  edx, PROTOCOL_ERROR
    jmp  enqueue_stream_error
stream_flow_error:
    mov  edx, FLOW_CONTROL_ERROR
enqueue_stream_error:
    mov  rcx, rbx
    call h2_enqueue_error
    jmp  frame_parse_loop

connection_compression_error:
    mov  edx, COMPRESSION_ERROR
    jmp  enqueue_connection_error
connection_flow_error:
    mov  edx, FLOW_CONTROL_ERROR
    jmp  enqueue_connection_error
connection_protocol_error:
    mov  edx, PROTOCOL_ERROR
    jmp  enqueue_connection_error
connection_internal_error:
    mov  edx, INTERNAL_ERROR
enqueue_connection_error:
    mov  rcx, rbx
    call h2_enqueue_error
    jmp  connection_draining

connection_shutdown:
    mov  rcx, rbx
    mov  edx, NO_ERROR
    call h2_enqueue_goaway
    cmp  eax, GOAWAY_QUEUE_FAILURE
    je   connection_goaway_failure
connection_draining: @frontier_or_measure(control_queue_or_drain_deadline)
    jmp  connection_schedule

connection_goaway_failure:
    mov  rcx, rbx
    call h2_mark_exact_teardown_suffix_disposition
    jmp  connection_close

connection_peer_close:
connection_io_error:
connection_close: @discharge exact_socket_and_connection_custody(rsi,rbx)
    mov  rcx, rsi
    call qword ptr [rip+__imp_closesocket]
    mov  rsi, INVALID_SOCKET
    mov  rcx, rbx
    call h2_release_connection_state
connection_closed_boundary: @cancellation_point exact_connection_custody_discharged
    mov  eax, dword ptr [rip+shutdown] @atomic(.acquire)
    test eax, eax
    jz   accept_wait

worker_return: @return_worker_loans
    xor  eax, eax
    add  rsp, 56
    pop  r15
    pop  r14
    pop  r13
    pop  r12
    pop  rdi
    pop  rsi
    pop  rbp
    pop  rbx
    ret
}

end Grass.Spikes.WebServer
```

### `Cancellation.lean`

```lean
import Grass.Process.Cancellation
import Spikes.«4_Web_Server».Process

namespace Grass.Spikes.WebServer

def hpackSliceStateProtocol :
    CommittedWorkingStateProtocol (Hpack.DecoderState protocolProfile) where
  beginWorking := Hpack.beginSlice
  mutateWorking := Hpack.decodeBoundedSlice
  commit := Hpack.commitCompletedSlice
  abandon := Hpack.returnLastCommitted
  workingPrivate := Hpack.workingSlicePrivate
  commitExact := Hpack.commitCompletedSliceExact
  abandonExact := Hpack.returnLastCommittedExact

def hpackSliceSummary :
    CancellationSummary (Hpack.decodeSliceProcess protocolProfile) :=
  CancellationSummary.uncancellableWorkingSlice
    (Hpack.decodeSliceCorrect protocolProfile)
    (.stepsAtMost Hpack.decodeSliceStepBound)
    hpackSliceStateProtocol

def hpackBetweenSlices :
    CancellationSummary (Hpack.betweenSlicesProcess protocolProfile) :=
  CancellationSummary.cancelPoint
    Hpack.betweenSlicesSafe
    Hpack.pendingCancellationCustody
    Hpack.cancelPreservesCommittedDecoderState

def hpackLoopSummary :
    CancellationSummary (Hpack.decodeLoopProcess protocolProfile) :=
  CancellationSummary.loop
    (CancellationSummary.seq hpackSliceSummary hpackBetweenSlices)
    Hpack.everyContinuingIterationConsumesInput
    Hpack.everyContinuingIterationCrossesCancelPoint

def hpackDecoderCancellation : CancellationSummary hpackDecoderProcess :=
  CancellationSummary.transport
    (Hpack.decoderDecomposesIntoSlices protocolProfile)
    hpackLoopSummary

def receiveReadinessCall :
    CancellationSummary Std.Process.Network.pollReadable :=
  CancellationSummary.uncancellableCall
    Std.Win32.Winsock.pollReadableCorrect
    (.providerReturnsWithin resourcePolicy.pollQuantum)

def receiveReadinessObservation :
    CancellationSummary Http2.afterReadablePollPoint :=
  CancellationSummary.cancelPoint
    Http2.afterReadablePollSafe
    Http2.pendingConnectionCancellationCustody
    Http2.observeCancellationAfterReadablePoll

def receiveCall :
    CancellationSummary Std.Process.Network.receive :=
  CancellationSummary.uncancellableCall
    Std.Win32.Winsock.nonblockingReceiveCorrect
    (.providerBounded Std.Win32.Winsock.nonblockingReceiveBound)

def receiveResultObservation :
    CancellationSummary Http2.afterReceiveResultPoint :=
  CancellationSummary.cancelPoint
    Http2.afterReceiveResultSafe
    Http2.pendingConnectionCancellationCustody
    Http2.observeCancellationAfterReceiveResult

def receiveCancellation :
  CancellationSummary Http2.receiveByteSegment :=
  CancellationSummary.transport Http2.receiveByteSegmentDecomposition
    (CancellationSummary.seq receiveReadinessCall
      (CancellationSummary.seq receiveReadinessObservation
        (CancellationSummary.seq receiveCall receiveResultObservation)))

def sendReadinessCall :
    CancellationSummary Std.Process.Network.pollWritable :=
  CancellationSummary.uncancellableCall
    Std.Win32.Winsock.pollWritableCorrect
    (.providerReturnsWithin resourcePolicy.pollQuantum)

def sendReadinessObservation :
    CancellationSummary Http2.afterWritablePollPoint :=
  CancellationSummary.cancelPoint
    Http2.afterWritablePollSafe
    Http2.pendingWriterCancellationCustody
    Http2.observeCancellationAfterWritablePoll

def sendCall :
    CancellationSummary Std.Process.Network.send :=
  CancellationSummary.uncancellableCall
    Std.Win32.Winsock.nonblockingSendCorrect
    (.providerBounded Std.Win32.Winsock.nonblockingSendBound)

def commitSentPrefixSummary :
    CancellationSummary Http2.commitSentPrefixProcess :=
  CancellationSummary.uncancellable
    Http2.commitSentPrefixCorrect
    (.stepsAtMost Http2.commitSentPrefixStepBound)

def completedFrameCancelPoint :
    CancellationSummary Http2.completedFrameCustodyPoint :=
  CancellationSummary.cancelPoint
    Http2.completedFrameCustodySafe
    Http2.pendingWriterCancellationCustody
    Http2.cancelAtFrameBoundaryByCause

def partialSendIterationCancellation :
    CancellationSummary Http2.partialSendIterationProcess :=
  CancellationSummary.seq sendReadinessCall
    (CancellationSummary.seq sendReadinessObservation
      (CancellationSummary.seq sendCall commitSentPrefixSummary))

def partialSendCancellation :
    CancellationSummary Http2.partialSendSegment :=
  CancellationSummary.transport Http2.partialSendSegmentDecomposition
    (CancellationSummary.seq
      (CancellationSummary.loop partialSendIterationCancellation
        Http2.remainingSuffixDecreasesOrProviderFrontier
        Http2.everyContinuingPartialSendIterationReachesReadinessObservation)
      completedFrameCancelPoint)

def flowCreditWaitCancellation :
    CancellationSummary Http2.flowCreditWaitProcess :=
  CancellationSummary.cancelPoint
    Http2.flowCreditWaitSafe
    Http2.pendingStreamCancellationCustody
    Http2.cancelReturnsUnselectedDataCredit

def streamTransitionSummary :
    CancellationSummary Http2.streamTransitionProcess :=
  CancellationSummary.uncancellable
    Http2.streamTransitionCorrect
    (.stepsAtMost Http2.streamTransitionStepBound)

def streamIterationCancellation :
    CancellationSummary Http2.streamIterationProcess :=
  CancellationSummary.choice
    (CancellationSummary.seq streamTransitionSummary flowCreditWaitCancellation)
    partialSendCancellation
    Http2.streamIterationBranchJoin

def streamCancellation : CancellationSummary streamProcess :=
  CancellationSummary.transport Http2.streamProcessDecomposition
    (CancellationSummary.loop streamIterationCancellation
      Http2.streamIterationProgress
      Http2.everyContinuingStreamIterationCrossesCancelPoint)

def connectionParseSummary :
    CancellationSummary Http2.connectionParseProcess :=
  CancellationSummary.uncancellable
    Http2.connectionParseCorrect
    (.stepsAtMost Http2.connectionParseStepBound)

def goawayDrainCancelPoint :
    CancellationSummary Http2.goawayDrainPoint :=
  CancellationSummary.cancelPoint
    Http2.goawayDrainSafe
    Http2.pendingConnectionCancellationCustody
    Http2.cancelPublishesGoawayAndFreezesAdmittedPrefix

def connectionIterationCancellation :
    CancellationSummary Http2.connectionIterationProcess :=
  CancellationSummary.choice
    (CancellationSummary.seq receiveCancellation connectionParseSummary)
    (CancellationSummary.choice partialSendCancellation
      (CancellationSummary.seq flowCreditWaitCancellation goawayDrainCancelPoint)
      Http2.writerOrDrainBranchJoin)
    Http2.receiveOrWriteBranchJoin

def connectionLoopCancellation : CancellationSummary connectionProcess :=
  CancellationSummary.transport Http2.connectionProcessDecomposition
    (CancellationSummary.loop connectionIterationCancellation
      Http2.connectionIterationProgress
      Http2.everyContinuingConnectionIterationCrossesCancelPoint)

def writerIterationCancellation :
    CancellationSummary Http2.writerIterationProcess :=
  CancellationSummary.choice
    partialSendCancellation
    flowCreditWaitCancellation
    Http2.writerBranchJoin

def connectionWriterCancellation :
    CancellationSummary connectionWriterProcess :=
  CancellationSummary.transport Http2.connectionWriterProcessDecomposition
    (CancellationSummary.loop writerIterationCancellation
      Http2.writerIterationProgress
      Http2.everyContinuingWriterIterationCrossesCancelPoint)

def connectionChildrenCancellation :
    CancellationSummary (Http2.connectionChildrenProcess processPolicy.connection) :=
  CancellationSummary.parallel
    hpackDecoderCancellation
    connectionWriterCancellation
    streamCancellation
    Http2.connectionChildAddressedCancellation
    Http2.connectionChildJoinDisposition

def connectionCancellation : CancellationSummary connectionProcess :=
  CancellationSummary.supervisor
    connectionLoopCancellation
    connectionChildrenCancellation
    Http2.goawayDrainSupervisorPolicy
    Http2.noForcedStopOutsideConnectionSafePoint

def workerAcceptCancellation :
    CancellationSummary (FixedPool.workerProcess processPolicy) :=
  CancellationSummary.loop
    (CancellationSummary.choice
      (CancellationSummary.seq
        (CancellationSummary.cancelPoint
          FixedPool.acceptLoopObservationSafe
          FixedPool.pendingWorkerCancellationCustody
          FixedPool.observeCancellationBeforeAcceptPoll)
        (CancellationSummary.seq
          (CancellationSummary.uncancellableCall
            Std.Win32.Winsock.pollAcceptCorrect
            (.providerReturnsWithin resourcePolicy.pollQuantum))
          (CancellationSummary.uncancellableCall
            Std.Win32.Winsock.nonblockingAcceptCorrect
            (.providerBounded Std.Win32.Winsock.nonblockingAcceptBound))))
      connectionCancellation
      FixedPool.acceptOrConnectionBranchJoin)
    FixedPool.workerIterationProgress
    FixedPool.everyContinuingWorkerIterationCrossesCancelPoint

def rootShutdownCancelPoint :
    CancellationSummary (FixedPool.rootShutdownPoint processPolicy) :=
  CancellationSummary.cancelPoint
    FixedPool.rootShutdownSafe
    FixedPool.pendingShutdownCustody
    FixedPool.shutdownStopsAdmission

def rootServiceCancellation :
    CancellationSummary (FixedPool.serverRootProcess processPolicy) :=
  CancellationSummary.loop
    (CancellationSummary.seq
      rootShutdownCancelPoint
      (CancellationSummary.uncancellableCall
        Std.Win32.Sleep.correct
        (.providerReturnsWithin resourcePolicy.pollQuantum)))
    FixedPool.rootServiceIterationProgress
    FixedPool.everyRootIterationCrossesShutdownPoint

def serverCancellation : CancellationSummary memoryServerProcess :=
  CancellationSummary.transport FixedPool.memoryServerProcessDecomposition
    (CancellationSummary.supervisor
      rootServiceCancellation
      (CancellationSummary.parallelFamily workerAcceptCancellation)
      FixedPool.serverShutdownPolicy
      FixedPool.noForcedWorkerStopWithLiveCustody)

theorem streamCancellationExports :
    ∃ contract, streamCancellation.exportedContract = some contract :=
  CancellationSummary.loop_exports
    Http2.everyContinuingStreamIterationCrossesCancelPoint

theorem hpackDecoderCancellationExports :
    ∃ contract, hpackDecoderCancellation.exportedContract = some contract :=
  CancellationSummary.loop_exports
    Hpack.everyContinuingIterationCrossesCancelPoint

theorem connectionWriterCancellationExports :
    ∃ contract, connectionWriterCancellation.exportedContract = some contract :=
  CancellationSummary.loop_exports
    Http2.everyContinuingWriterIterationCrossesCancelPoint

theorem connectionCancellationExports :
    ∃ contract, connectionCancellation.exportedContract = some contract :=
  CancellationSummary.supervisor_exports
    (CancellationSummary.loop_exports
      Http2.everyContinuingConnectionIterationCrossesCancelPoint)
    (CancellationSummary.parallel_exports
      hpackDecoderCancellationExports connectionWriterCancellationExports
      streamCancellationExports)
    Http2.goawayDrainSupervisorPolicy

theorem workerAcceptCancellationExports :
    ∃ contract, workerAcceptCancellation.exportedContract = some contract :=
  CancellationSummary.loop_exports
    FixedPool.everyContinuingWorkerIterationCrossesCancelPoint

theorem rootServiceCancellationExports :
    ∃ contract, rootServiceCancellation.exportedContract = some contract :=
  CancellationSummary.loop_exports
    FixedPool.everyRootIterationCrossesShutdownPoint

theorem serverCancellationExports :
    ∃ contract, serverCancellation.exportedContract = some contract :=
  CancellationSummary.supervisor_exports
    rootServiceCancellationExports
    (CancellationSummary.parallelFamily_exports workerAcceptCancellationExports)
    FixedPool.serverShutdownPolicy

theorem serverExportedContractCompatibleWithSupervisor :
    ExportedContractCompatibleWithSupervisor
      serverCancellation FixedPool.supervisorPolicy :=
  FixedPool.serverExportedContractCompatible
    serverCancellationExports

def serverTerminationFacet :
    TerminationFacet memoryServerCorrect
      (.supervised FixedPool.supervisorPolicy) :=
  CancellationSummary.toSupervisedTerminationFacet
    serverCancellation memoryServerCorrect FixedPool.supervisorPolicy
    serverCancellationExports serverExportedContractCompatibleWithSupervisor

theorem cancellationSequenceRegroupingIsIrrelevant :
    CancellationSummary.seq
      receiveReadinessCall
      (CancellationSummary.seq receiveReadinessObservation receiveCall) =
    CancellationSummary.transportProcessAssoc
      (CancellationSummary.seq
        (CancellationSummary.seq receiveReadinessCall receiveReadinessObservation)
        receiveCall) :=
  CancellationSummary.seq_assoc _ _ _

theorem streamResetCancelsOnlyAddressedIncarnation
    (connection : ConnectionId) (stream : Http2StreamId) :
    CancellationRequestAt serverCancellation (.stream connection stream) .deadline
      ⟹ EventuallyExactDisposition
        (.finishCurrentFrameThenRst stream .cancel ∨
          .connectionTeardownWithExactSuffixDisposition connection stream)
        (.preserveSiblingsUntilConnectionTeardown connection stream) :=
  streamCancellation.addressedDisposition connection stream

theorem writableSurvivingConnectionEventuallyResetsAddressedStream
    (connection : ConnectionId) (stream : Http2StreamId)
    (writable : EventuallyWritableForCurrentFrame connection)
    (survives : ConnectionSurvivesUntilFrameBoundary connection)
    (fair : WriterScheduledFairly connection) :
    CancellationRequestAt serverCancellation (.stream connection stream) .deadline
      ⟹ EventuallyExactDisposition
        (.finishCurrentFrameThenRst stream .cancel)
        (.preserveSiblingStreams connection stream) :=
  streamCancellation.rstAfterFinish writable survives fair

theorem blockedFlowControlRemainsCancellable
    (stream : Http2StreamId) :
    AtFlowCreditWait stream ⟹
      EventuallyExactDisposition
        (.enqueueRstWithoutDataCredit stream .cancel)
        (.preserveSiblingStreamsByControlQueue stream) :=
  schedulerCancellationConsumer.enqueueRstForFlowBlocked stream

theorem partialSendCancellationPreservesCommittedPrefix
    (frame : Http2.SerializedFrame) (committed : Fin (frame.bytes.size + 1)) :
    CancelAfterSendResult frame committed ⟹
      ExactPartialFrameCancellationDisposition
        (committedPrefix := frame.bytes.take committed)
        (remainingSuffix := frame.bytes.drop committed)
        (streamCancel := .finishFrameThenReset)
        (connectionCancel := .finishFrameOrCloseConnection) :=
  partialSendCancellation.dispositionAtFrameBoundaryOrTeardown frame committed

theorem hpackCancellationPreservesLastCommittedState
    (committed working : Hpack.DecoderState protocolProfile)
    (started : Hpack.WorkingSliceStartedFrom committed working)
    (mutation : Hpack.WorkingMutationOf committed working) :
    CancellationDuringDecode committed working ⟹
      Eventually
        (CancellationReturnsExactly committed ∨
          ∃ successor,
            Hpack.SliceFinishesToCommittedSuccessor committed working successor ∧
            CancellationReturnsExactly successor) :=
  hpackDecoderCancellation.delayAndDisposition committed working started mutation

theorem streamCancellationDoesNotCancelHpackDecoder
    (connection : ConnectionId) (stream : Http2StreamId) :
    ¬ CancellationAddresses
      (.stream connection stream) (.hpackDecoder connection) :=
  Http2.streamCancellationDoesNotAddressConnectionDecoder connection stream

theorem gracefulConnectionCancellationPublishesPrefix
    (connection : ConnectionId) :
    CancellationRequestAt serverCancellation (.connection connection) .shutdown
      ⟹ EventuallyGoawayDrainOrFailedClose connection :=
  connectionCancellation.supervisedDisposition connection

theorem goawayDrainProgressOrExactEscalation
    (connection : ConnectionId) :
    GoawayPublished connection ⟹
      (DrainPremises connection → EventuallyDrainedAndClosed connection) ∧
      (DrainDeadlineExceeded connection →
        EventuallyExactTeardownWithSuffixDisposition connection) :=
  connectionCancellation.drainProgressOrEscalation connection

theorem repeatedShutdownObservationDoesNotConsumeControlCapacity
    (connection : ConnectionId) :
    GoawayPublished connection →
      ReobserveShutdown connection →
      ControlQueueSlotsAfter connection = ControlQueueSlotsBefore connection ∧
      FrozenLastStreamIdAfter connection = FrozenLastStreamIdBefore connection :=
  Http2.beginGracefulShutdownIdempotent

theorem normalAndFailedTerminalsAreExhaustive :
    EveryCancellationTerminal serverCancellation
      (.normalDischarged ∨ .failedWithDeclaredAdoption) :=
  serverCancellation.terminalBoundaryComplete

theorem noCancellationInsideHpackMutation :
    ¬ CancellationSafePoint hpackDecoderCancellation
      Hpack.ControlPoint.midDynamicTableMutation :=
  hpackDecoderCancellation.notSafeInsideSlice

theorem noCancellationBeforeSentPrefixCommit :
    ¬ CancellationSafePoint partialSendCancellation
      Http2.ControlPoint.sendReturnedBeforePrefixCommit :=
  partialSendCancellation.notSafeBeforeCustodyRestored

theorem noForcedWorkerStopWithLiveSocket :
    ¬ PermittedForcedCancellation serverCancellation
      FixedPool.ControlPoint.workerOwnsLiveSocket :=
  serverCancellation.noForcedStop

theorem uncancellableInfiniteCallCannotClaimBoundedCancellation
    (call : ProcessSpec) (correct : ProcessCorrect call)
    (forever : MayBlockForeverWithoutEnvironmentFrontier call) :
    (CancellationSummary.uncancellable correct .environmentPending).exportedContract =
      none :=
  CancellationSummary.uncancellable_exports_none correct forever

theorem plainSerialLeafNeedsNoRichCancellationFacet
    (function : RegisteredSerialFunction) :
    CancellationSummary function.process =
      CancellationSummary.weakestUncancellable function.correct :=
  rfl

theorem serverProcessPlanRealizes :
    ProcessPlanRealizes spec serverProcessPlan := by
  exact FixedPool.weaveCorrect
    serverComposition serverTerminationFacet
    memoryServerCorrect connectionCorrect streamCorrect frameParserCorrect
    hpackDecoderCorrect connectionWriterCorrect
    Std.Process.Network.allCorrect Std.Process.Clock.allCorrect
    Std.Process.Supervision.allCorrect Std.Process.Resource.closeHandleCorrect
    Std.Process.System.shutdownSignalCorrect
    Std.Process.Terminal.finishCorrect

def connectionScope (id : ConnectionId) : ProcessScope serverProcessPlan :=
  ProcessScope.descendantsOf (.connection id)

theorem connectionMemoryBound (id : ConnectionId) :
    EveryExecutionUsesAtMost
      (connectionScope id)
      ServerResourceMetric.grassOwnedResidentBytes
      (Http2.connectionBytes processPolicy) :=
  serverProcessPlanRealizes.resources.subgraphBound
    (ServerBoundaryFlux.connection id)

def streamScope (connection : ConnectionId) (stream : Http2StreamId) :
    ProcessScope serverProcessPlan :=
  ProcessScope.descendantsOf (.stream connection stream)

theorem streamMemoryBound (connection : ConnectionId) (stream : Http2StreamId) :
    EveryExecutionUsesAtMost
      (streamScope connection stream)
      ServerResourceMetric.grassOwnedResidentBytes
      (Http2.streamBytes processPolicy) :=
  serverProcessPlanRealizes.resources.subgraphBound
    (ServerBoundaryFlux.stream connection stream)

theorem connectionStreamBound (id : ConnectionId) :
    EveryReachableStateSatisfies
      (ActiveStreams id ≤ resourcePolicy.maxConcurrentStreamsPerConnection) :=
  serverProcessPlanRealizes.resources.capacityBound

theorem serverSocketBound :
    EveryExecutionUsesAtMost
      ProcessScope.root
      ServerResourceMetric.socketDescriptors
      resourcePolicy.maxSocketDescriptors :=
  serverProcessPlanRealizes.resources.rootBound

theorem serverHandleBound :
    EveryExecutionUsesAtMost
      ProcessScope.root
      ServerResourceMetric.windowsHandles
      (ServerResourceBudget.handles processPolicy) :=
  serverProcessPlanRealizes.resources.rootBound

def serverResourceAxisRealization : ResourceAxisRealizationFamily spec :=
  ResourceAxisRealizationFamily.fromCapturedSemantics spec.resourceSemantics

theorem serverResourceAxisKeysInjective :
    Function.Injective serverResourceAxisRealization.concreteKey :=
  serverResourceAxisRealization.keyInjective

theorem serverRootResidentMemoryBound :
    EveryExecutionUsesAtMost
      ProcessScope.root
      ServerResourceMetric.grassOwnedResidentBytes
      (ServerResourceBudget.residentBytes resourcePolicy) :=
  serverProcessPlanRealizes.resources.rootBound

theorem serverRootResourceEquation :
    ExactRootResourceEquation
      serverProcessPlan serverResourceAxisRealization
      (ServerResourceBudget.allAxes resourcePolicy) :=
  serverProcessPlanRealizes.resources.rootEquation

end Grass.Spikes.WebServer
```

### `Macros.lean`

```lean
import Grass.Assembly.X86
import Spikes.«4_Web_Server».Process

namespace Grass.Spikes.WebServer

def routeBody : ByteArray := body

def bindAddress : ByteArray :=
  #[0x02, 0x00, 0x1f, 0x90, 0x7f, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

def serverSettings : Http2.Settings :=
  { headerTableSize := resourcePolicy.hpackDecoderTableBytes
    enablePush := false
    maxConcurrentStreams := resourcePolicy.maxConcurrentStreamsPerConnection
    initialWindowSize := resourcePolicy.inboundStreamWindow
    maxFrameSize := 16384
    maxHeaderListSize := resourcePolicy.maxHeaderListBytes }

def clientPreface : ByteArray :=
  "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n".toUTF8

def settingsFrame : ByteArray :=
  Http2.Frame.write (.settings false serverSettings)

def successFields : Http2.HeaderList :=
  [(.status, "200"), (.name "content-type", "text/plain"),
   (.name "content-length", toDecimalBytes routeBody.size)]

def successHeaderBlock : ByteArray :=
  Hpack.encodeWithoutIndexing successFields

def notFoundFields : Http2.HeaderList :=
  [(.status, "404"), (.name "content-length", "0")]

def notFoundHeaderBlock : ByteArray :=
  Hpack.encodeWithoutIndexing notFoundFields

def connectionStateBytes : Nat :=
  Http2.ConnectionLayout.bytes resourcePolicy

def streamStateBytes : Nat :=
  Http2.StreamLayout.bytes resourcePolicy

def workerSlotBytes : Nat :=
  Http2.WorkerSlotLayout.bytes resourcePolicy

theorem settingsRoundTrip :
    Http2.Frame.parse protocolProfile settingsFrame =
      .ok (.settings false serverSettings) :=
  Http2.Frame.parse_write protocolProfile _ serverSettings.admissible

theorem successHeaderBlockDecodes :
    Hpack.decode Hpack.emptyDecoder successHeaderBlock =
      .ok (Hpack.emptyDecoder, successFields) :=
  Hpack.decode_encodeWithoutIndexing _

def serverStaticObjects : StaticObjectTable := static_objects {
  rodata align 16 {
    route_body: bytes routeBody
    bind_address: bytes bindAddress
    client_preface: bytes clientPreface
    settings_frame: bytes settingsFrame
    success_header_block: bytes successHeaderBlock
    not_found_header_block: bytes notFoundHeaderBlock
    hpack_huffman_decode_table: bytes Hpack.huffmanDecodeTableBytes
    hpack_static_table: bytes Hpack.staticTableBytes
  }
  data align 64 {
    shutdown: uint32 0
    fatal: uint32 0
    start_gate: uint32 0
    nonblocking_one: uint32 0
    listen_socket: uint64 0xffffffffffffffff
    worker_handles: zero 32
    wsa_data: zero 408
    worker_slots: zero (executionEnvelope.workerCount * workerSlotBytes)
    connection_states: zero (executionEnvelope.connectionCapacity * connectionStateBytes)
    stream_states: zero (executionEnvelope.connectionCapacity *
      resourcePolicy.maxConcurrentStreamsPerConnection * streamStateBytes)
  }
}

structure LocalFragmentBody
    (entry : BlockContract) (exits : FragmentExitFamily entry) where
  name : Name
  algorithm : X86.FragmentAlgorithm entry exit
  rawExpansion : RawInstructionListing
  expandsExactly : algorithm.lower = rawExpansion
  references : ExactInternalReferenceManifest rawExpansion
  citations : InstructionAndProtocolCitationManifest rawExpansion
  machine : FragmentMachineCertificate rawExpansion entry exits references.imports

def LocalFragmentBody.fragment (body : LocalFragmentBody entry exits) :
    VerifiedFragment entry exits where
  source := body.algorithm.authoredSource
  expanded := body.rawExpansion
  expansionExact := body.expandsExactly
  localCorrect := body.machine.localCorrect
  citations := body.citations.instructionCoverage

def consumePrefaceBody :
    LocalFragmentBody Http2.X86.Contract.consumePrefaceEntry
      Http2.X86.Contract.consumePrefaceExit := x86_fragment_body {
  name := `consumeClientPreface
  state := connection.readPointer, connection.haveBytes
  input := clientPreface
  algorithm := requireBytes 24
    |> compareExactBytes
    |> choose needInput protocolError
    |> onSuccess (advanceRing 24)
}

def parseFrameHeaderBody (maxFrameSize : Nat) :
    LocalFragmentBody (Http2.X86.Contract.parseHeaderEntry maxFrameSize)
      Http2.X86.Contract.parseHeaderExit := x86_fragment_body {
  name := `parseFrameHeader
  state := connection.frameLength, connection.frameType,
    connection.frameFlags, connection.frameStream, connection.payloadPointer
  algorithm := requireBytes 9
    |> loadBe24 0 frameLength
    |> requireAtMost maxFrameSize connectionError
    |> requireBytes (9 + frameLength)
    |> loadU8 3 frameType
    |> loadU8 4 frameFlags
    |> loadBe32Masked 5 0x7fffffff frameStream
    |> publishPayloadPointer 9
}

def hpackIntegerBody :
    LocalFragmentBody Hpack.X86.Contract.integerEntry
      Hpack.X86.Contract.integerExit := x86_fragment_body {
  name := `decodeHpackInteger
  state := working.pointer, working.remaining, working.integerValue
  algorithm := loadPrefix
    |> loopWhile continuationBitSet {
      requireByte
      checkedShiftAdd 7
      rejectShiftAtLeast 64 compressionError
    }
    |> rejectNonMinimalInteger compressionError
    |> publishInteger
}

def hpackHuffmanBody :
    LocalFragmentBody Hpack.X86.Contract.huffmanEntry
      Hpack.X86.Contract.huffmanExit := x86_fragment_body {
  name := `decodeHpackHuffman
  state := working.encodedPointer, working.encodedRemaining,
    working.decodedPointer, working.decodedBytes
  tables := hpackHuffmanDecodeTable
  algorithm := bitstreamLoop {
      canonicalPrefixLookup
      rejectSymbol eos compressionError
      requireOutputBelow resourcePolicy.maxHeaderListBytes
      appendDecodedSymbol
    }
    |> requireFinalPaddingAtMost 7
    |> requireFinalPaddingEosPrefix
}

def hpackStringBody :
    LocalFragmentBody Hpack.X86.Contract.stringEntry
      Hpack.X86.Contract.stringExit := x86_fragment_body {
  name := `decodeHpackString
  children := hpackIntegerBody, hpackHuffmanBody
  algorithm := decodeLength hpackIntegerBody
    |> requireInputLength
    |> chooseBy huffmanFlag (decodeWith hpackHuffmanBody) copyPlainBytes
    |> requireDecodedTotalAtMost resourcePolicy.maxHeaderListBytes
}

def hpackFieldSectionBody (tableBytes headerListBytes : Nat) :
    LocalFragmentBody (Hpack.X86.Contract.fieldSectionEntry tableBytes headerListBytes)
      Hpack.X86.Contract.fieldSectionExit := x86_fragment_body {
  name := `decodeHpackFieldSection
  children := hpackIntegerBody, hpackStringBody
  state := committedDecoder, privateWorkingDecoder
  algorithm := copyCommittedToPrivateWorking
    |> loopUntilBlockEnd {
      classifyRepresentation
      indexed => decodeInteger |> exactStaticOrDynamicLookup |> appendField
      literalIndexed => decodeName |> decodeValue |> insertAndEvictTo tableBytes |> appendField
      literal => decodeName |> decodeValue |> appendField
      tableSize => requireBeforeFirstField |> decodeInteger |> resizeAndEvictTo tableBytes
    }
    |> requireHeaderListAtMost headerListBytes
    |> onSuccess commitPrivateWorkingAtomically
    |> onError discardPrivateWorking
}

def beginHeaderBlockBody (capacity : Nat) :
    LocalFragmentBody (Http2.X86.Contract.beginHeaderBlockEntry capacity)
      Http2.X86.Contract.beginHeaderBlockExit := x86_fragment_body {
  name := `beginHeaderBlock
  state := connection.continuationStream, connection.continuationBytes
  algorithm := requireFrameType headers
    |> requireNoOpenContinuation
    |> requireNonzeroStream
    |> checkedBeginHeaderPayloadAtMost capacity
    |> consumeFrame
}

def continuationBody (capacity : Nat) :
    LocalFragmentBody (Http2.X86.Contract.continuationEntry capacity)
      Http2.X86.Contract.continuationExit := x86_fragment_body {
  name := `appendContinuation
  state := connection.continuationStream, connection.continuationBytes
  algorithm := requireFrameType continuation
    |> requireSameNonzeroStream
    |> checkedAppendPayloadAtMost capacity
    |> consumeFrame
    |> finishOnlyWhen endHeaders
}

def dispatchBody (profile : Http2.Profile) :
    LocalFragmentBody (Http2.X86.Contract.dispatchEntry profile)
      Http2.X86.Contract.dispatchExit := x86_fragment_body {
  name := `dispatchFrame
  algorithm := validateLengthStreamAndFlags profile
    |> tableDispatch data headers priority rstStream settings pushPromise
      ping goaway windowUpdate continuation
    |> unknownType ignorePayload
    |> forbiddenPush connectionError
}

def initialSettingsBody :
    LocalFragmentBody Http2.X86.Contract.initialSettingsEntry
      Http2.X86.Contract.initialSettingsExit := x86_fragment_body {
  name := `requireInitialSettings
  algorithm := ifNot peerSettingsSeen
    (requireType settings |> requireNotAck)
    accept
}

def requestFieldsBody :
    LocalFragmentBody Http2.X86.Contract.requestFieldsEntry
      Http2.X86.Contract.requestFieldsExit := x86_fragment_body {
  name := `validateRequestFields
  algorithm := rejectUppercaseNames
    |> rejectConnectionSpecificFields
    |> requirePseudoHeadersBeforeRegular
    |> requireExactlyOne method
    |> requireExactlyOne path
    |> allowOptional scheme authority
    |> requireMethod get
    |> exactStaticRouteMatch routes
}

def settingsBody (settings : Http2.Settings) :
    LocalFragmentBody (Http2.X86.Contract.settingsEntry settings)
      Http2.X86.Contract.settingsExit := x86_fragment_body {
  name := `applySettings
  algorithm := validateAckAndLength
    |> foldSixByteEntriesRejectInvalid
    |> requireEnablePushZero
    |> checkedInitialWindowDeltaAcrossOpenStreams
    |> boundHeaderTable resourcePolicy.hpackDecoderTableBytes
    |> publishPeerSettings
    |> enqueueAckOnce
}

def windowUpdateBody :
    LocalFragmentBody Http2.X86.Contract.windowUpdateEntry
      Http2.X86.Contract.windowUpdateExit := x86_fragment_body {
  name := `applyWindowUpdate
  algorithm := requirePayloadLength 4
    |> loadBe32Masked 0 0x7fffffff increment
    |> rejectZeroByScope
    |> checkedAddCreditByScope 0x7fffffff
    |> wakeEligibleWriters
}

def streamTransitionBody :
    LocalFragmentBody Http2.X86.Contract.streamTransitionEntry
      Http2.X86.Contract.streamTransitionExit := x86_fragment_body {
  name := `transitionStream
  state := boundedStreamSlots, highestPeerStream, streamIncarnations
  algorithm := validatePeerStreamParityAndMonotonicity
    |> lookupOrClaimBoundedIncarnation
    |> transitionBy frameType frameFlags streamState
    |> classifyErrorScope
}

def boundedQueueBody (kind : Http2.QueueKind) (capacity : Nat) :
    LocalFragmentBody (Http2.X86.Contract.queueEntry kind capacity)
      Http2.X86.Contract.queueExit := x86_fragment_body {
  name := `boundedQueue
  state := queue.head, queue.tail, queue.slots
  algorithm := reserveSlotAtMost capacity
    |> writeCompleteFrameDescriptor
    |> publishTailRelease
    |> onFull returnQueueFullWithoutMutation
}

def staticResponseBody (headerBlock payload : ByteArray) :
    LocalFragmentBody Http2.X86.Contract.staticResponseEntry
      Http2.X86.Contract.staticResponseExit := x86_fragment_body {
  name := `enqueueStaticResponse
  children := boundedQueueBody
  constants := headerBlock, payload
  algorithm := reserveExactResponseDescriptors
    |> writeHeadersDescriptor headerBlock endHeaders
    |> ifPayloadEmpty setEndStreamOnHeaders
    |> otherwiseWriteDataDescriptor payload endStream
    |> publishAllDescriptorsOrNoneRelease
}

def scopedErrorBody :
    LocalFragmentBody Http2.X86.Contract.scopedErrorEntry
      Http2.X86.Contract.scopedErrorExit := x86_fragment_body {
  name := `enqueueScopedError
  children := boundedQueueBody
  algorithm := inspectLatchedErrorScope
    |> streamScope (writeRstStreamDescriptor exactStreamIncarnation)
    |> connectionScope (writeGoawayDescriptor lastAcceptedStream)
    |> reserveAndPublishExactlyOneControlSlot
}

def inboundCreditBody :
    LocalFragmentBody Http2.X86.Contract.inboundCreditEntry
      Http2.X86.Contract.inboundCreditExit := x86_fragment_body {
  name := `debitInboundCredit
  algorithm := requireLengthWithinConnectionCredit
    |> requireLengthWithinStreamCredit
    |> debitBothAtomically
    |> classifyFlowErrorByScope
}

def releaseInboundBody :
    LocalFragmentBody Http2.X86.Contract.releaseInboundEntry
      Http2.X86.Contract.releaseInboundExit := x86_fragment_body {
  name := `releaseInboundData
  algorithm := restoreConsumedCredit
    |> coalesceConnectionWindowUpdate
    |> coalesceStreamWindowUpdate
    |> enqueueOnlyWithinControlBound
}

def outboundCreditBody :
    LocalFragmentBody Http2.X86.Contract.outboundCreditEntry
      Http2.X86.Contract.outboundCreditExit := x86_fragment_body {
  name := `debitOutboundCredit
  algorithm := chooseMin frameBytes connectionCredit streamCredit
    |> onZero returnFlowBlocked
    |> debitChosenPrefixExactly
}

def rstBody :
    LocalFragmentBody Http2.X86.Contract.rstEntry
      Http2.X86.Contract.rstExit := x86_fragment_body {
  name := `applyRstStream
  algorithm := requireNonzeroStream
    |> requirePayloadLength 4
    |> closeExactStreamIncarnation
    |> releaseDischargedStreamCustody
}

def peerGoawayBody :
    LocalFragmentBody Http2.X86.Contract.peerGoawayEntry
      Http2.X86.Contract.peerGoawayExit := x86_fragment_body {
  name := `applyPeerGoaway
  algorithm := requireConnectionScope
    |> requirePayloadAtLeast 8
    |> recordMonotonePeerLastStream
    |> enterPeerDrain
}

def pingBody :
    LocalFragmentBody Http2.X86.Contract.pingEntry
      Http2.X86.Contract.pingExit := x86_fragment_body {
  name := `acknowledgePing
  algorithm := requireConnectionScope
    |> requirePayloadLength 8
    |> ifNot ackFlag (copyPayload |> enqueueControlAck) consumeFrame
}

def outboundSelectionBody :
    LocalFragmentBody Http2.X86.Contract.selectOutboundEntry
      Http2.X86.Contract.selectOutboundExit := x86_fragment_body {
  name := `selectOutbound
  algorithm := preferMandatoryControl
    |> otherwiseRoundRobinStreams
    |> requirePositiveConnectionAndStreamCreditForData
    |> capPayloadByCreditsAndMaxFrame
}

def hasOutboundBody :
    LocalFragmentBody Http2.X86.Contract.hasOutboundEntry
      Http2.X86.Contract.hasOutboundExit := x86_fragment_body {
  name := `hasSendableOutbound
  algorithm := controlQueueNonempty
    |> orAnyBoundedStreamWithDataAndBothCredits
}

def serializeFrameBody :
    LocalFragmentBody Http2.X86.Contract.serializeFrameEntry
      Http2.X86.Contract.serializeFrameExit := x86_fragment_body {
  name := `serializeSelectedFrame
  algorithm := writeBe24Length
    |> writeTypeFlags
    |> writeBe31StreamId
    |> copySelectedPayloadWithinTransmitBound
    |> publishWholeFrameCustody
}

def commitPrefixBody :
    LocalFragmentBody Http2.X86.Contract.commitPrefixEntry
      Http2.X86.Contract.commitPrefixExit := x86_fragment_body {
  name := `commitSentPrefix
  algorithm := requireProviderCountAtMostRemaining
    |> advanceSendPointer
    |> subtractRemaining
    |> transferExactPrefixCustodyToEnvironment
}

def releaseStreamsBody :
    LocalFragmentBody Http2.X86.Contract.releaseClosedEntry
      Http2.X86.Contract.releaseClosedExit := x86_fragment_body {
  name := `releaseClosedStreams
  algorithm := boundedSlotScan resourcePolicy.maxConcurrentStreamsPerConnection {
    releaseOnlyIf closedAndAllCustodyDischarged
  }
}

def cancelExpiredBody (bound : Nat) :
    LocalFragmentBody (Http2.X86.Contract.cancelExpiredEntry bound)
      Http2.X86.Contract.cancelExpiredExit := x86_fragment_body {
  name := `cancelExpiredStreams
  algorithm := boundedSlotScan bound {
    ifDeadlineExpired
      (publishStreamCancellationCause
        |> ifNoFrameInFlight enqueueRstWithoutDataCredit)
  }
}

def connectionDeadlineBody (deadline : Duration) :
    LocalFragmentBody (Http2.X86.Contract.deadlineEntry deadline)
      Http2.X86.Contract.deadlineExit := x86_fragment_body {
  name := `checkConnectionDeadline
  imports := GetTickCount64
  algorithm := call GetTickCount64
    |> wrappingElapsedSince lastProgressTick
    |> compareAtLeast deadline
}

def initializeConnectionBody :
    LocalFragmentBody Http2.X86.Contract.initializeEntry
      Http2.X86.Contract.initializeExit := x86_fragment_body {
  name := `initializeConnection
  algorithm := claimBoundedConnectionSlot
    |> zeroConnectionAndStreamStorage
    |> initializeLocalAndPeerWindows serverSettings
    |> initializeBoundedRingAndQueues
    |> clearGoawayPublication
    |> enqueueInitialSettings
}

def receiveRingBody (capacity : Nat) :
    LocalFragmentBody (Network.X86.Contract.receiveRingEntry capacity)
      Network.X86.Contract.receiveRingExit := x86_fragment_body {
  name := `receiveIntoRing
  imports := recv
  algorithm := computeWritableRingSuffix
    |> callNonblockingRecv
    |> requireProviderCountAtMostSuffix
    |> commitPositivePrefix
    |> preserveStateOnWouldBlockOrError
}

def pollReadableBody :
    LocalFragmentBody Network.X86.Contract.pollReadableEntry
      Network.X86.Contract.pollReadableExit := x86_fragment_body {
  name := `pollReadable
  imports := WSAPoll
  algorithm := buildSingleReadablePollFd
    |> callBounded WSAPoll resourcePolicy.pollQuantum
    |> classifyReadyTimeoutError
}

def pollWritableBody :
    LocalFragmentBody Network.X86.Contract.pollWritableEntry
      Network.X86.Contract.pollWritableExit := x86_fragment_body {
  name := `pollWritable
  imports := WSAPoll
  algorithm := buildSingleWritablePollFd
    |> callBounded WSAPoll resourcePolicy.pollQuantum
    |> classifyReadyTimeoutError
}

def ignoredPriorityBody :
    LocalFragmentBody Http2.X86.Contract.priorityEntry
      Http2.X86.Contract.priorityExit := x86_fragment_body {
  name := `validateIgnoredPriority
  algorithm := requireNonzeroStream
    |> requirePayloadLength 5
    |> consumeFrameWithoutPriorityState
}

def unknownPayloadBody :
    LocalFragmentBody Http2.X86.Contract.unknownEntry
      Http2.X86.Contract.unknownExit := x86_fragment_body {
  name := `consumeUnknownPayload
  algorithm := requireCompletePayload |> consumeFrameWithoutStateChange
}

def localGoawayBody :
    LocalFragmentBody Http2.X86.Contract.localGoawayEntry
      Http2.X86.Contract.localGoawayExit := x86_fragment_body {
  name := `beginGracefulShutdown
  state := connection.goawayPublished, connection.drainState
  algorithm := atomicExchange goawayPublished 1
    |> ifPreviouslyOne returnAlreadyPublishedSuccess
    |> reserveOneControlSlot
    |> onSuccess (writeGoawayFromLatchedError |> publishControlTailRelease |> enterDrain)
    |> onFailure (atomicStore goawayPublished 0 |> returnQueueFailure)
}

def drainedBody :
    LocalFragmentBody Http2.X86.Contract.drainEntry
      Http2.X86.Contract.drainExit := x86_fragment_body {
  name := `shouldCloseDrained
  algorithm := allAcceptedStreamsTerminal
    |> andAllOutboundCustodyDischarged
    |> orDrainDeadlineRequiresExactTeardown
}

def releaseConnectionBody :
    LocalFragmentBody Http2.X86.Contract.releaseConnectionEntry
      Http2.X86.Contract.releaseConnectionExit := x86_fragment_body {
  name := `releaseConnection
  algorithm := dischargeOrAdoptEveryStreamObligation
    |> returnAllQueueBufferAndHpackTokens
    |> returnConnectionSlot
}

def teardownSuffixBody :
    LocalFragmentBody Http2.X86.Contract.teardownSuffixEntry
      Http2.X86.Contract.teardownSuffixExit := x86_fragment_body {
  name := `markExactTeardownSuffixDisposition
  algorithm := snapshotCommittedPrefixAndUnsentSuffix
    |> transferSuffixCustodyToConnectionTeardown
}

def writerObservationBody :
    LocalFragmentBody Http2.X86.Contract.writerObservationEntry
      Http2.X86.Contract.writerObservationExit := x86_fragment_body {
  name := `observeWriterCancellation
  algorithm := atomicLoadCancellationCauseAcquire
    |> ifNoCause continueWriting
    |> ifFrameComplete finishThenRstAddressedStream
    |> ifConnectionCause closeWithExactSuffixDisposition
    |> otherwiseContinueCurrentFrame
}

def frameOf (body : LocalFragmentBody entry exits) : VerifiedFragment entry exits :=
  body.fragment

def parseFrameHeaderMacro := (frameOf (parseFrameHeaderBody 16384)).asTransparentMacro
def consumeClientPrefaceMacro := (frameOf consumePrefaceBody).asTransparentMacro
def decodeFieldSectionMacro := (frameOf (hpackFieldSectionBody resourcePolicy.hpackDecoderTableBytes resourcePolicy.maxHeaderListBytes)).asTransparentMacro
def beginHeaderBlockMacro := (frameOf (beginHeaderBlockBody resourcePolicy.maxContinuationBytes)).asTransparentMacro
def appendContinuationMacro := (frameOf (continuationBody resourcePolicy.maxContinuationBytes)).asTransparentMacro
def dispatchFrameMacro := (frameOf (dispatchBody protocolProfile)).asTransparentMacro
def requireInitialSettingsMacro := (frameOf initialSettingsBody).asTransparentMacro
def validateRequestFieldsMacro := (frameOf requestFieldsBody).asTransparentMacro
def applySettingsMacro := (frameOf (settingsBody serverSettings)).asTransparentMacro
def applyWindowUpdateMacro := (frameOf windowUpdateBody).asTransparentMacro
def transitionStreamMacro := (frameOf streamTransitionBody).asTransparentMacro
def enqueueControlMacro := (frameOf (boundedQueueBody .control resourcePolicy.maxQueuedControlFramesPerConnection)).asTransparentMacro
def enqueueResponseMacro := (frameOf (staticResponseBody successHeaderBlock routeBody)).asTransparentMacro
def enqueueNotFoundMacro := (frameOf (staticResponseBody notFoundHeaderBlock #[])).asTransparentMacro
def enqueueErrorMacro := (frameOf scopedErrorBody).asTransparentMacro
def debitInboundCreditMacro := (frameOf inboundCreditBody).asTransparentMacro
def releaseInboundDataMacro := (frameOf releaseInboundBody).asTransparentMacro
def debitOutboundCreditMacro := (frameOf outboundCreditBody).asTransparentMacro
def applyRstStreamMacro := (frameOf rstBody).asTransparentMacro
def applyGoawayMacro := (frameOf peerGoawayBody).asTransparentMacro
def acknowledgePingMacro := (frameOf pingBody).asTransparentMacro
def selectOutboundMacro := (frameOf outboundSelectionBody).asTransparentMacro
def hasSendableOutboundMacro := (frameOf hasOutboundBody).asTransparentMacro
def serializeSelectedFrameMacro := (frameOf serializeFrameBody).asTransparentMacro
def commitSentPrefixMacro := (frameOf commitPrefixBody).asTransparentMacro
def releaseClosedStreamsMacro := (frameOf releaseStreamsBody).asTransparentMacro
def cancelExpiredStreamsMacro := (frameOf (cancelExpiredBody resourcePolicy.maxConcurrentStreamsPerConnection)).asTransparentMacro
def checkConnectionDeadlineMacro := (frameOf (connectionDeadlineBody resourcePolicy.connectionIdleDeadline)).asTransparentMacro
def initializeConnectionMacro := (frameOf initializeConnectionBody).asTransparentMacro
def receiveIntoRingMacro := (frameOf (receiveRingBody resourcePolicy.maxReceiveBytesPerConnection)).asTransparentMacro
def pollConnectionMacro := (frameOf pollReadableBody).asTransparentMacro
def pollWritableMacro := (frameOf pollWritableBody).asTransparentMacro
def validateIgnoredPriorityMacro := (frameOf ignoredPriorityBody).asTransparentMacro
def consumeUnknownPayloadMacro := (frameOf unknownPayloadBody).asTransparentMacro
def enqueueGoawayMacro := (frameOf localGoawayBody).asTransparentMacro
def shouldCloseDrainedMacro := (frameOf drainedBody).asTransparentMacro
def releaseConnectionMacro := (frameOf releaseConnectionBody).asTransparentMacro
def markTeardownSuffixDispositionMacro := (frameOf teardownSuffixBody).asTransparentMacro
def observeWriterCancellationMacro := (frameOf writerObservationBody).asTransparentMacro

theorem enqueueGoawayMacroIdempotent :
    RepeatedSuccessConsumesNoAdditionalControlSlot
      enqueueGoawayMacro Http2.ConnectionField.goawayPublished :=
  localGoawayBody.machine.goawayPublicationIdempotent

def serverMacros : MacroTable platformPlan := macros {
  h2_consume_preface => consumeClientPrefaceMacro
  h2_parse_frame_header => parseFrameHeaderMacro
  hpack_decode_field_section => decodeFieldSectionMacro
  h2_begin_header_block => beginHeaderBlockMacro
  h2_append_continuation => appendContinuationMacro
  h2_dispatch_frame => dispatchFrameMacro
  h2_require_initial_settings => requireInitialSettingsMacro
  h2_validate_request_fields => validateRequestFieldsMacro
  h2_apply_settings => applySettingsMacro
  h2_apply_window_update => applyWindowUpdateMacro
  h2_transition_stream => transitionStreamMacro
  h2_enqueue_control => enqueueControlMacro
  h2_enqueue_response => enqueueResponseMacro
  h2_enqueue_not_found => enqueueNotFoundMacro
  h2_enqueue_error => enqueueErrorMacro
  h2_debit_inbound_credit => debitInboundCreditMacro
  h2_release_inbound_data => releaseInboundDataMacro
  h2_debit_outbound_credit => debitOutboundCreditMacro
  h2_apply_rst_stream => applyRstStreamMacro
  h2_apply_goaway => applyGoawayMacro
  h2_ack_ping => acknowledgePingMacro
  h2_select_outbound => selectOutboundMacro
  h2_has_sendable_outbound => hasSendableOutboundMacro
  h2_serialize_selected_frame => serializeSelectedFrameMacro
  h2_commit_sent_prefix => commitSentPrefixMacro
  h2_release_closed_streams => releaseClosedStreamsMacro
  h2_cancel_expired_streams => cancelExpiredStreamsMacro
  h2_check_connection_deadline => checkConnectionDeadlineMacro
  h2_initialize_connection_state => initializeConnectionMacro
  receive_into_ring => receiveIntoRingMacro
  connection_poll => pollConnectionMacro
  poll_connection_writable => pollWritableMacro
  h2_validate_ignored_priority => validateIgnoredPriorityMacro
  h2_consume_unknown_payload => consumeUnknownPayloadMacro
  h2_enqueue_goaway => enqueueGoawayMacro
  h2_should_close_drained => shouldCloseDrainedMacro
  h2_release_connection_state => releaseConnectionMacro
  h2_mark_exact_teardown_suffix_disposition => markTeardownSuffixDispositionMacro
  h2_observe_writer_cancellation => observeWriterCancellationMacro
}

def serverFragmentHierarchy : FragmentExpansionHierarchy platformPlan := hierarchy {
  root serverMacros
  shard framing consumePrefaceBody parseFrameHeaderBody beginHeaderBlockBody continuationBody dispatchBody
  shard hpack hpackIntegerBody hpackHuffmanBody hpackStringBody hpackFieldSectionBody
  shard state initialSettingsBody requestFieldsBody settingsBody windowUpdateBody
    streamTransitionBody rstBody peerGoawayBody pingBody ignoredPriorityBody unknownPayloadBody
  shard queues boundedQueueBody staticResponseBody scopedErrorBody
    inboundCreditBody releaseInboundBody outboundCreditBody
    outboundSelectionBody hasOutboundBody serializeFrameBody commitPrefixBody
  shard lifecycle initializeConnectionBody receiveRingBody pollReadableBody pollWritableBody
    releaseStreamsBody cancelExpiredBody connectionDeadlineBody localGoawayBody drainedBody
    releaseConnectionBody teardownSuffixBody writerObservationBody
}

theorem serverFragmentHierarchyComplete :
    EverySelectedOperationHasExactlyOneLocalConstructorBody
      serverMacros serverFragmentHierarchy := by
  validate_fragment_hierarchy

theorem serverFragmentExpansionExact :
    HierarchicalExpansionExactlyEqualsFlatMacroExpansion
      serverFragmentHierarchy serverMacros :=
  FragmentExpansionHierarchy.flatten_exact serverFragmentHierarchy

theorem serverMacrosTransparent :
    EveryMacroExpandsToExactRawInstructions serverMacros :=
  serverFragmentExpansionExact.everyMacroExact

theorem serverMacrosCancellationTransparent :
    EveryMacroExpansionPreservesCancellationMasksSafePointsAndCustody
      serverMacros :=
  serverFragmentHierarchy.cancellationTransparent

end Grass.Spikes.WebServer
```

### `Process.lean`

```lean
import Grass.Process
import Grass.Platform.Win10.X64
import Grass.Std.Http2.Model
import Grass.Std.Http2.Process
import Grass.Std.Hpack.Model
import Grass.Std.Process.Network
import Grass.Std.Process.Supervision
import Spikes.«4_Web_Server».Spec

namespace Grass.Spikes.WebServer

def executionEnvelope : Win32ServerExecutionEnvelope where
  workerCount := 4
  connectionCapacity := 4
  streamCapacityPerConnection := 128
  hpackDecoderStorageBytes := 4096
  maxQueuedControlFramesPerConnection := 32
  maxQueuedDataBytesPerConnection := 65535
  maxReceiveBytesPerConnection := 32768
  maxTransmitBytesPerConnection := 65535
  maxSocketDescriptors := 5
  maxThreadHandles := 4
  pollQuantum := .milliseconds 10
  storage := .fixedAfterReady

def resourcePolicy : MemoryServerResourcePolicy :=
  executionEnvelope.materialize capturedSemanticBudget

theorem executionEnvelopeRealizesSemanticBudget :
    RealizesSemanticBudget executionEnvelope capturedSemanticBudget := by
  simpa [capturedSemanticBudgetExact] using
    Win32ServerExecutionEnvelope.materialize_sound executionEnvelope semanticBudget

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10Http2PriorKnowledge
    (endpoint := .ipv4Loopback 8080)
    (gracefulShutdownStatus := 0)
    (startupFailureStatus := 1)

def protocolProfile : Http2.Profile where
  transport := .cleartextPriorKnowledge
  maxFrameSize := capturedSemanticBudget.maxInboundFrameBytes
  serverPush := false
  priorityMode := .ignoreDeprecated
  extensionMode := .ignoreUnknown
  hpackDynamicTableBytes := capturedSemanticBudget.hpackDecoderTableBytes
  maxHeaderListBytes := capturedSemanticBudget.maxHeaderListBytes

def connectionModel : Http2.ConnectionModel :=
  Http2.ConnectionModel.server protocolProfile behaviorPolicy routes

def frameParserRealizes : ParserRealizes frameFormat
    (Http2.Frame.parseResult protocolProfile) :=
  Http2.Frame.parserRealizesFormat protocolProfile

def hpackParserRealizes : ParserRealizes hpackFieldSectionFormat
    (Hpack.FieldSection.parseResult protocolProfile) :=
  Hpack.FieldSection.parserRealizesFormat protocolProfile

theorem frameWriterRoundTrip (frame : Http2.Frame)
    (admissible : frame.Admissible protocolProfile) :
    Http2.Frame.parse protocolProfile (Http2.Frame.write frame) = .ok frame :=
  Http2.Frame.parse_write protocolProfile frame admissible

theorem frameParserConforms (input : ByteArray) :
    Http2.Frame.parse protocolProfile input = .error ∨
    ∃ frame suffix,
      Http2.Frame.parsePrefix protocolProfile input = .ok (frame, suffix) ∧
      frame.Admissible protocolProfile ∧
      input = Http2.Frame.write frame ++ suffix :=
  Http2.Frame.parse_conforms protocolProfile input

def platformPlan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64Http2FixedPool projection

inductive ServerRoleSchema
  | listener
  | connection
  | stream

def ServerRoleSchema.Instance : ServerRoleSchema -> Type
  | .listener => Unit
  | .connection => ConnectionId
  | .stream => ConnectionId × Http2StreamId

def connectionSession (id : ConnectionId) : SpecProcess resources :=
  Http2.abstractConnectionSession resources routes behaviorPolicy id

def streamSession (connection : ConnectionId) (stream : Http2StreamId) :
    SpecProcess resources :=
  Http2.abstractRequestStream resources routes behaviorPolicy connection stream

def abstractServer : AbstractSpecificationProcessNetwork resources :=
  Http2.abstractMemoryServer
    (roleSchema := ServerRoleSchema)
    (instances := ServerRoleSchema.Instance)
    (routes := routes)
    (connection := connectionSession)
    (stream := streamSession)
    (admission := WebServerResources.connectionCapacity resources)
    (custody := .linearPerConnectionAndStream)

def serverProcessPresentation : ProcessPresentation spec where
  network := abstractServer
  denotationExact := Http2.abstractMemoryServerDenotesContract
  requirementsExact := Http2.abstractMemoryServerRequirementsExact

def processPolicy : MemoryServerProcessPolicy :=
  MemoryServerProcessPolicy.ofSpecification spec
    |>.withHpackEncoder .literalWithoutIndexing

inductive ServerCommand
  | beginListening (endpoint : Endpoint)
  | acceptArrival (arrival : ArrivalId)
  | cancelConnection (id : ConnectionId) (reason : CancelReason)
  | initiateShutdown
  | finish (outcome : ServerOutcome)

inductive ConnectionCommand
  | receiveBytes (id : ConnectionId) (capacity : CapacityCredit .bytes)
  | emitFrames (id : ConnectionId) (frames : List Http2.OutboundFrame)
  | spawnStream (connection : ConnectionId) (stream : Http2StreamId)
  | cancelStream (connection : ConnectionId) (stream : Http2StreamId)
      (reason : CancelReason)
  | closeConnection (id : ConnectionId) (error : Option Http2.ErrorCode)

inductive StreamCommand
  | acceptFields (fields : Http2.HeaderList)
  | acceptData (bytes : ByteArray) (credit : Http2.FlowCredit)
  | grantInboundCredit (increment : Http2.WindowIncrement)
  | requestResponse (route : RouteId)
  | reset (error : Http2.ErrorCode)
  | expire

def memoryServerProcess : ProcessSpec where
  Request := Unit
  State := MemoryServerState routes processPolicy
  TerminalResult := ServerOutcome
  ExternalEvent := ServerExternalEvent
  Demand := ServerCommand
  Result := ServerResponse
  Observation := ServerObservation
  Initial := MemoryServerState.InitialWithDemands
  Terminal := MemoryServerState.Terminal
  Step := MemoryServerState.Step
  view := some
    { View := ServerDesiredState
      render := MemoryServerState.desired }

def connectionProcess : ProcessSpec :=
  Grass.Std.Http2.connectionProcess routes processPolicy.connection

def streamProcess : ProcessSpec :=
  Grass.Std.Http2.streamProcess routes processPolicy.stream

def frameParserProcess : ProcessSpec :=
  SequentialAdapter.parserProcess frameParserRealizes

def hpackDecoderProcess : ProcessSpec :=
  Grass.Std.Hpack.decoderProcess protocolProfile

def connectionWriterProcess : ProcessSpec :=
  Grass.Std.Http2.connectionWriterProcess processPolicy.connection

inductive ServerApiProtocol
  | winsockSession
  | listenerCreate
  | listenerBind
  | listenerListen
  | listenerMode
  | poll
  | accept
  | receive
  | send
  | lastNetworkError
  | closeSocket
  | workerCreate
  | workerResume
  | workerJoin
  | handleClose
  | monotonicSample
  | boundedYield
  | shutdownRegistration
  | terminal

def ServerApiProtocol.process : ServerApiProtocol → ProcessSpec
  | .winsockSession => Std.Process.Network.session
  | .listenerCreate => Std.Process.Network.createListener
  | .listenerBind => Std.Process.Network.bind
  | .listenerListen => Std.Process.Network.listen
  | .listenerMode => Std.Process.Network.setMode
  | .poll => Std.Process.Network.poll
  | .accept => Std.Process.Network.accept
  | .receive => Std.Process.Network.receive
  | .send => Std.Process.Network.send
  | .lastNetworkError => Std.Process.Network.lastError
  | .closeSocket => Std.Process.Network.close
  | .workerCreate => Std.Process.Supervision.createWorker
  | .workerResume => Std.Process.Supervision.resumeWorker
  | .workerJoin => Std.Process.Supervision.joinWorker
  | .handleClose => Std.Process.Resource.closeHandle
  | .monotonicSample => Std.Process.Clock.sample
  | .boundedYield => Std.Process.Clock.boundedYield
  | .shutdownRegistration => Std.Process.System.shutdownSignal
  | .terminal => Std.Process.Terminal.finish processPolicy.terminalPolicy

inductive ServerProtocolKey
  | root
  | listener
  | worker (slot : Fin executionEnvelope.workerCount)
  | connection
  | stream
  | hpackDecoder
  | connectionWriter
  | frameParser
  | api (protocol : ServerApiProtocol)
  | terminal

def serverProtocols : ProtocolRegistry where
  Key := ServerProtocolKey
  protocol
    | .root => memoryServerProcess
    | .listener => Std.Process.Network.listener
    | .worker slot => FixedPool.workerProtocol slot
    | .connection => connectionProcess
    | .stream => streamProcess
    | .hpackDecoder => hpackDecoderProcess
    | .connectionWriter => connectionWriterProcess
    | .frameParser => frameParserProcess
    | .api protocol => protocol.process
    | .terminal => Std.Process.Terminal.finish processPolicy.terminalPolicy

inductive ServerProcessKind
  | root
  | listener
  | worker (slot : Fin executionEnvelope.workerCount)
  | connection (id : ConnectionId)
  | stream (connection : ConnectionId) (id : Http2StreamId)
  | hpackDecoder (connection : ConnectionId)
  | connectionWriter (connection : ConnectionId)
  | frameParser (connection : ConnectionId) (demand : DemandId)
  | apiCall (id : DemandId) (protocol : ServerApiProtocol)
  | terminal

inductive ServerSharedRegion
  | routeBody
  | shutdownRequested
  | fatalState
  | initializationGate
  | listenerAuthority

def serverProcessPlan : ProcessPlan serverProtocols spec.driverBoundary where
  ProcessKind := ServerProcessKind
  SharedRegion := ServerSharedRegion
  SharedState := ServerSharedState routes processPolicy
  protocolKey
    | .root => .root
    | .listener => .listener
    | .worker slot => .worker slot
    | .connection _ => .connection
    | .stream _ _ => .stream
    | .hpackDecoder _ => .hpackDecoder
    | .connectionWriter _ => .connectionWriter
    | .frameParser _ _ => .frameParser
    | .apiCall _ protocol => .api protocol
    | .terminal => .terminal
  root := .root
  rootBoundary := server_root_exposes_boundary
  maySpawn := ServerSpawnLaw
  sharedAccess := ServerLogicalAccess
  population := ServerPopulationLaw
  ChannelKind := ServerChannelKind
  endpoints := ServerChannelEndpoints
  channel := ServerChannelContracts
  boundaryProjection := ServerBoundaryProjection
  spawn := ServerSpawnAuthority
  cancellation := ServerCancellationLaw
  supervision := ServerSupervisionLaw

def memoryServerCorrect : ProcessCorrect memoryServerProcess where
  Invariant := MemoryServerState.Invariant routes processPolicy
  initial := MemoryServerState.initialInvariant
  initialDemands := MemoryServerState.initialDemandsWellFormed
  preserved := MemoryServerState.stepPreservesInvariant
  terminal := MemoryServerState.terminalAccepts
  terminalNoStep := MemoryServerState.terminalNoStep
  viewAccepts := MemoryServerState.desiredAccepts
  observationsAccept := MemoryServerState.observationsAccept
  demandsWellFormed := MemoryServerState.demandsWellFormed
  progress := MemoryServerState.progress

def connectionCorrect : ProcessCorrect connectionProcess :=
  Grass.Std.Http2.connectionCorrect routes processPolicy.connection

def streamCorrect : ProcessCorrect streamProcess :=
  Grass.Std.Http2.streamCorrect routes processPolicy.stream

def frameParserCorrect : ProcessCorrect frameParserProcess :=
  SequentialAdapter.parserProcessCorrect frameParserRealizes

def hpackDecoderCorrect : ProcessCorrect hpackDecoderProcess :=
  Grass.Std.Hpack.decoderProcessCorrect protocolProfile

def connectionWriterCorrect : ProcessCorrect connectionWriterProcess :=
  Grass.Std.Http2.connectionWriterProcessCorrect processPolicy.connection

structure ServerCompositionWitness where
  startupSilence : BeforeReadyNoProtocolBytesAreEmitted serverProcessPlan
  fixedStorage : ReadyImpliesNoFutureAllocationDemand serverProcessPlan
  socketGeneration : SocketIdentityAndGenerationInvariant serverProcessPlan
  listenerAuthority : ExactlyOneListenerAuthority serverProcessPlan
  admissionPermits : ActiveConnectionsCorrespondToPermits
    serverProcessPlan resourcePolicy.maxActiveConnections
  workerSlots : DisjointWorkerSlotOwnership serverProcessPlan
  receiveCancelRace : EveryReceiveLoanHasOneRaceWinner serverProcessPlan
  sendCancelRace : EverySendSuffixHasOneRaceWinner serverProcessPlan
  receiveFragments : PositiveReceivesAppendExactByteChunks serverProcessPlan
  sendPrefixes : PositiveSendsCommitExactPrefixes serverProcessPlan
  deadlineCorrelation : DeadlinesTargetExactConnectionGeneration serverProcessPlan
  streamGeneration : StreamIdentityMonotonicAndNeverReused serverProcessPlan
  streamLifecycle : EveryFrameRespectsHttp2StreamState serverProcessPlan
  continuation : HeaderBlockContinuationIsConnectionExclusive serverProcessPlan
  hpackState : HpackContextsAreOrderedBoundedAndConnectionLocal serverProcessPlan
  hpackValidity : EveryAcceptedFieldSectionHasValidRfc7541Decoding serverProcessPlan
  hpackCancellationRouting : StreamCancellationNeverTargetsConnectionHpackState serverProcessPlan
  flowControl : ConnectionAndStreamCreditsConserved serverProcessPlan
  flowBackpressure : ExhaustedCreditPreventsDataAdmissionAndEmission serverProcessPlan
  controlProgress : ControlFramesNeverConsumeDataCredit serverProcessPlan
  frameCoverage : EveryRfc9113FrameKindHasDeclaredTransition serverProcessPlan
  errorScope : EveryProtocolErrorHasRfc9113Scope serverProcessPlan
  unknownExtensions : UnknownExtensionFramesAreIgnoredWithoutStateCorruption serverProcessPlan
  noPush : PushPromiseIsConnectionProtocolError serverProcessPlan
  deprecatedPriority : PrioritySignalsDoNotAffectBehavior serverProcessPlan
  settings : SettingsApplyAtomicallyBeforeAcknowledgement serverProcessPlan
  settingsWindowRebase : PeerInitialWindowRebasePreservesSignedCredit serverProcessPlan
  ping : PingAcknowledgementsPreserveExactOpaquePayload serverProcessPlan
  goaway : GoawayPreservesProcessedStreamPrefix serverProcessPlan
  outputOrder : ConnectionWriterSerializesFramesAndPreservesStreamOrder serverProcessPlan
  streamCancellation : EveryStuckStreamHasOneCancelRaceWinner serverProcessPlan
  workerReuse : ReuseRequiresJoinAndFreshGeneration serverProcessPlan
  shutdown : ShutdownPublicationAndCustodyInvariant serverProcessPlan
  routeSharing : ImmutableRouteBodySharedReadOnly serverProcessPlan
  obligations : ExactNetworkObligationPartition serverProcessPlan
  resources : ExactServerResourcePartition serverProcessPlan

def serverComposition : ServerCompositionWitness where
  startupSilence := server_startup_silence
  fixedStorage := server_fixed_after_ready
  socketGeneration := server_socket_generation
  listenerAuthority := server_listener_authority
  admissionPermits := server_admission_permits
  workerSlots := server_worker_slots
  receiveCancelRace := server_receive_cancel_race
  sendCancelRace := server_send_cancel_race
  receiveFragments := server_receive_fragments
  sendPrefixes := server_send_prefixes
  deadlineCorrelation := server_deadline_correlation
  streamGeneration := server_stream_generation
  streamLifecycle := server_stream_lifecycle
  continuation := server_continuation_exclusion
  hpackState := server_hpack_state
  hpackValidity := server_hpack_validity
  hpackCancellationRouting := server_hpack_cancellation_routing
  flowControl := server_flow_credit
  flowBackpressure := server_flow_backpressure
  controlProgress := server_control_progress
  frameCoverage := server_frame_coverage
  errorScope := server_error_scope
  unknownExtensions := server_unknown_extensions
  noPush := server_no_push
  deprecatedPriority := server_priority_ignored
  settings := server_settings_order
  settingsWindowRebase := server_settings_window_rebase
  ping := server_ping_payload
  goaway := server_goaway_prefix
  outputOrder := server_output_order
  streamCancellation := server_stream_cancellation
  workerReuse := server_worker_reuse
  shutdown := server_shutdown_custody
  routeSharing := server_route_sharing
  obligations := server_obligation_partition
  resources := server_resource_partition

end Grass.Spikes.WebServer
```

### `Program.lean`

```lean
import Grass.Emit
import Grass.Artifact.PE32Plus
import Spikes.«4_Web_Server».Assembly
import Spikes.«4_Web_Server».Cancellation

namespace Grass.Spikes.WebServer

def serverVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    using explicit_process serverProcessPlanRealizes
    using_cancellation serverCancellation
    with serverSource

def bytes : ByteArray := emitProgram serverVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  serverVerified.sound

def artifact : PE32Plus := serverVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem parserConforms (input : ByteArray) :
    PE32Plus.parse input = .error ∨
    ∃ image, PE32Plus.parse input = .ok image ∧
      PE32Plus.ConformsToSpecification input image :=
  PE32Plus.parserConforms input

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact serverVerified.rawProgram :=
  serverVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

theorem admissibleLoadsRefineHttp2 :
    ∀ load ∈ PE32Plus.admissibleLoads bytes,
      LoadedExecutionRefines load spec :=
  serverVerified.artifactCorrectness.everyAdmissibleLoad

end Grass.Spikes.WebServer
```

### `Spec.lean`

```lean
import Grass.Spec.Http2
import Grass.Spec.Grammar
import Grass.Spec.Resource

namespace Grass.Spikes.WebServer

def semanticBudget : Http2ServerSemanticBudget where
  maxActiveConnections := 4
  maxConcurrentStreamsPerConnection := 128
  maxHeaderListBytes := 16384
  hpackDecoderTableBytes := 4096
  hpackEncoderTableBytes := 0
  maxInboundFrameBytes := 16384
  maxContinuationBytes := 16384
  inboundConnectionWindow := 65535
  inboundStreamWindow := 65535
  outboundConnectionWindowCeiling := 2147483647
  outboundStreamWindowCeiling := 2147483647
  streamProgressDeadline := .seconds 5
  connectionIdleDeadline := .seconds 30

def resources : ServerResourceModel :=
  ServerResourceModel.http2 semanticBudget

def body : ByteArray := "Grass web server\n".toUTF8

def routes : Http2Routes :=
  .singleton { method := .GET, scheme := .http, authority := .any,
    path := "/".toASCII, response :=
      { status := 200, fields := [("content-type", "text/plain")], body } }

def behaviorPolicyFor {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : Http2ServerBehaviorPolicy :=
  Http2ServerBehaviorPolicy.fromCapturedResources resources where
    transport := .cleartextPriorKnowledge
    acceptedVersion := .http2
    serverPush := false
    priority := .ignoreDeprecatedSignals
    unknownRoute := .responseStatus 404
    malformed := .rfc9113ScopedError
    unsupportedExtensionFrame := .ignore
    requestMethods := {.GET}
    requestBodies := .discardWithinFlowControl
    responseTrailers := false
    peerSettings := .applyAfterValidationThenAcknowledge
    ping := .acknowledgeOpaquePayload
    goaway := .gracefulPrefix
    connectionWindowUpdates := .rfc9113
    streamWindowUpdates := .rfc9113
    hpackDecoderTableBytes := WebServerResources.hpackDecoderTableBytes resources
    maxHeaderListBytes := WebServerResources.maxHeaderListBytes resources
    initialConnectionWindow := WebServerResources.inboundConnectionWindow resources
    initialStreamWindow := WebServerResources.inboundStreamWindow resources
    hpackEncoder := .anyConformingEncoding
    huffman := .acceptValidRejectInvalid

def frameFormat : Format Http2.Frame :=
  Http2.frameFormat

def hpackFieldSectionFormat : Format Http2.HeaderList :=
  Hpack.fieldSectionFormat

def frameParserRequirement {R : Type} [ResourceModel R]
    (resources : R) : ProcessRequirement resources :=
  Format.parserRequirement frameFormat

def hpackParserRequirement {R : Type} [ResourceModel R]
    (resources : R) : ProcessRequirement resources :=
  Format.parserRequirement hpackFieldSectionFormat

def webServerSuite {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : SpecificationSuite resources :=
  Http2.memoryServerSuite
    resources routes (behaviorPolicyFor resources)
    (frameParserRequirement resources) (hpackParserRequirement resources)

def webServerSpec {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (webServerSuite resources)
    |>.withProgress
      { service := .reactive
        acceptedConnection := .settlesUnder
          [.schedulerFair, .monotonicClockAdvances, .environmentResponsive]
        termination := .under
          [.shutdownEventuallyRequested, .schedulerFair,
           .monotonicClockAdvances, .environmentResponsive] }

theorem webServerSpecCorrect {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : MeetsAllSpecificationTheorems (webServerSpec resources) :=
  Http2.memoryServerSuiteCaptureCorrect
    resources routes (behaviorPolicyFor resources)
    (frameParserRequirement resources) (hpackParserRequirement resources)

def spec : SpecProcess resources := webServerSpec resources

def behaviorPolicy : Http2ServerBehaviorPolicy := behaviorPolicyFor resources

def capturedSemanticBudget : Http2ServerSemanticBudget :=
  Http2ServerSemanticBudget.fromCapturedSemantics spec.resourceSemantics

theorem capturedSemanticBudgetExact : capturedSemanticBudget = semanticBudget :=
  SpecProcess.capturedResourceConstructionExact spec

end Grass.Spikes.WebServer
```
