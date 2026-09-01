# Spike 4: multiplexed in-memory HTTP/2 server to Win32 x86-64 PE

Status: design artifact for adversarial review; intentionally not compilable.

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

Resources parameterize the specification because flow control and admission are
observable. The typeclasses provide laws and named axes; the selected resource
value supplies reviewed limits.

```lean
def resourcePolicy : MemoryServerResourcePolicy where
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
  maxQueuedControlFramesPerConnection := 32
  maxQueuedDataBytesPerConnection := 65535
  maxReceiveBytesPerConnection := 32768
  maxTransmitBytesPerConnection := 65535
  maxSocketDescriptors := 5
  maxThreadHandles := 4
  pollQuantum := .milliseconds 10
  streamProgressDeadline := .seconds 5
  connectionIdleDeadline := .seconds 30
  storage := .fixedAfterReady

def resources : ServerResourceModel :=
  ServerResourceModel.http2 resourcePolicy

def spec : SpecProcess resources := webServerSpec resources

def behaviorPolicy : Http2ServerBehaviorPolicy := behaviorPolicyFor resources

def capturedResourcePolicy : MemoryServerResourcePolicy :=
  MemoryServerResourcePolicy.fromCapturedSemantics spec.resourceSemantics

theorem capturedResourcePolicyExact : capturedResourcePolicy = resourcePolicy :=
  SpecProcess.capturedResourceConstructionExact spec
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
  maxFrameSize := capturedResourcePolicy.maxInboundFrameBytes
  serverPush := false
  priorityMode := .ignoreDeprecated
  extensionMode := .ignoreUnknown
  hpackDynamicTableBytes := capturedResourcePolicy.hpackDecoderTableBytes
  maxHeaderListBytes := capturedResourcePolicy.maxHeaderListBytes

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
      next.dynamicTable.bytes ≤ capturedResourcePolicy.hpackDecoderTableBytes ∧
      fields.byteSize ≤ capturedResourcePolicy.maxHeaderListBytes
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
        (.providerReturnsWithin capturedResourcePolicy.pollQuantum)))
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
      (ActiveStreams id ≤ capturedResourcePolicy.maxConcurrentStreamsPerConnection)

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
      (ServerResourceBudget.residentBytes capturedResourcePolicy)

theorem serverRootResourceEquation :
    ExactRootResourceEquation serverProcessPlan serverResourceAxisRealization
      (ServerResourceBudget.allAxes capturedResourcePolicy)
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
    AssemblyNeverAllocatesAfterReady serverExpandedSource capturedResourcePolicy := by
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
    using_source_closure serverSourceClosureComplete
    using_expansion serverExpansionExact
    using_cancellation serverCfgCancellationRefines
    with serverExpandedSource

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
  Resource.lean
  Spec.lean
  Projection.lean
  Model.lean
  Process.lean
  Cancellation.lean
  Plan.lean
  Data.lean
  Macros.lean
  Assembly.lean
  SourceClosure.lean
  Bindings.lean
  Program.lean
  Artifact.lean
```

They intentionally contain no explanatory comments, `sorry`, `admit`, `axiom`,
`unsafe`, or decision-by-execution proof. This document owns the rationale and
proof commentary; the fixtures expose exactly the declarations and proof terms
the eventual libraries should let an author maintain.
