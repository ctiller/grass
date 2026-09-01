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
    (.providerReturnsWithin capturedResourcePolicy.pollQuantum)

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
    (.providerReturnsWithin capturedResourcePolicy.pollQuantum)

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
            (.providerReturnsWithin capturedResourcePolicy.pollQuantum))
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
      CancellationCanConsumeAt flowCreditWaitCancellation stream :=
  flowCreditWaitCancellation.safeAt _

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
      (ActiveStreams id ≤ capturedResourcePolicy.maxConcurrentStreamsPerConnection) :=
  serverProcessPlanRealizes.resources.capacityBound

theorem serverSocketBound :
    EveryExecutionUsesAtMost
      ProcessScope.root
      ServerResourceMetric.socketDescriptors
      capturedResourcePolicy.maxSocketDescriptors :=
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
      (ServerResourceBudget.residentBytes capturedResourcePolicy) :=
  serverProcessPlanRealizes.resources.rootBound

theorem serverRootResourceEquation :
    ExactRootResourceEquation
      serverProcessPlan serverResourceAxisRealization
      (ServerResourceBudget.allAxes capturedResourcePolicy) :=
  serverProcessPlanRealizes.resources.rootEquation

end Grass.Spikes.WebServer
