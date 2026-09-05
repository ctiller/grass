import Grass.Process
import Grass.Platform.Win10.X64
import Grass.Std.Protocol.Http2
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

def protocolProfile : Http2.Profile := protocolPackage.machineProfile

def connectionModel : Http2.ConnectionModel :=
  protocolPackage.connectionModel

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

def abstractServer : ProcessPresentationNetwork resources :=
  Http2.abstractMemoryServer
    (roleSchema := ServerRoleSchema)
    (instances := ServerRoleSchema.Instance)
    (routes := routes)
    (connection := connectionSession)
    (stream := streamSession)
    (admission := WebServerResources.connectionCapacity resources)
    (custody := .linearPerConnectionAndStream)

/-! The network is replaceable shape. The selected trace is separate, so the
network itself cannot silently become a second precious behavior specification. -/
def serverProcessPresentation : ProcessPresentation spec where
  network := abstractServer
  trace := Http2.abstractMemoryServerTrace
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

/-! Select the boundary vocabulary once. The HTTP/2 package supplies its
interruption, logical-fault, and environment-violation classes; ordinary
process literals do not restate them. -/
def serverVocabulary : ProcessVocabulary :=
  Http2.serverVocabulary
    ServerExternalEvent ServerCommand ServerResponse ServerObservation

def memoryServerProcess : ProcessSpec where
  vocabulary := serverVocabulary
  Request := Unit
  State := MemoryServerState routes processPolicy
  TerminalResult := ServerOutcome
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
