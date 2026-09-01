import Grass.Process.Cancellation
import Spikes.«4_Web_Server».Process

namespace Grass.Spikes.WebServer

def hpackSliceSummary :
    CancellationSummary (Hpack.decodeSliceProcess protocolProfile) :=
  CancellationSummary.uncancellable
    (Hpack.decodeSliceCorrect protocolProfile)
    (.stepsAtMost Hpack.decodeSliceStepBound)

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

def receiveReadinessCancellation :
    CancellationSummary Std.Process.Network.pollReadable :=
  CancellationSummary.interruptibleCall
    Std.Win32.Winsock.pollReadableInterruption

def receiveCallCancellation :
    CancellationSummary Std.Process.Network.receive :=
  CancellationSummary.interruptibleCall
    Std.Win32.Winsock.receiveInterruption

def receiveCancellation :
    CancellationSummary Http2.receiveByteSegment :=
  CancellationSummary.transport Http2.receiveByteSegmentDecomposition
    (CancellationSummary.seq receiveReadinessCancellation receiveCallCancellation)

def sendReadinessCancellation :
    CancellationSummary Std.Process.Network.pollWritable :=
  CancellationSummary.interruptibleCall
    Std.Win32.Winsock.pollWritableInterruption

def sendCallCancellation :
    CancellationSummary Std.Process.Network.send :=
  CancellationSummary.interruptibleCall
    Std.Win32.Winsock.sendInterruption

def commitSentPrefixSummary :
    CancellationSummary Http2.commitSentPrefixProcess :=
  CancellationSummary.uncancellable
    Http2.commitSentPrefixCorrect
    (.stepsAtMost Http2.commitSentPrefixStepBound)

def suffixCustodyCancelPoint :
    CancellationSummary Http2.unsentSuffixCustodyPoint :=
  CancellationSummary.cancelPoint
    Http2.unsentSuffixCustodySafe
    Http2.pendingWriterCancellationCustody
    Http2.cancelRoutesExactUnsentSuffixByCause

def partialSendCancellation :
    CancellationSummary Http2.partialSendSegment :=
  CancellationSummary.transport Http2.partialSendSegmentDecomposition
    (CancellationSummary.seq sendReadinessCancellation
      (CancellationSummary.seq sendCallCancellation
        (CancellationSummary.seq commitSentPrefixSummary
          suffixCustodyCancelPoint)))

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
      (CancellationSummary.interruptibleCall Std.Win32.Winsock.acceptInterruption)
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
      (CancellationSummary.interruptibleCall Std.Win32.Sleep.interruption)
      rootShutdownCancelPoint)
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
      receiveReadinessCancellation
      (CancellationSummary.seq receiveCallCancellation hpackSliceSummary) =
    CancellationSummary.transportProcessAssoc
      (CancellationSummary.seq
        (CancellationSummary.seq receiveReadinessCancellation receiveCallCancellation)
        hpackSliceSummary) :=
  CancellationSummary.seq_assoc _ _ _

theorem streamResetCancelsOnlyAddressedIncarnation
    (connection : ConnectionId) (stream : Http2StreamId) :
    CancellationRequestAt serverCancellation (.stream connection stream) .deadline
      ⟹ EventuallyExactDisposition
        (.rstStream stream .cancel)
        (.preserveSiblingStreams connection stream) :=
  streamCancellation.addressedDisposition connection stream

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
  partialSendCancellation.dispositionAtSuffixPoint frame committed

theorem hpackCancellationPreservesLastCommittedState
    (state : Hpack.DecoderState protocolProfile) :
    CancellationDuringDecode state ⟹
      EventuallyCancelsWithExactState hpackDecoderCancellation state :=
  hpackDecoderCancellation.delayAndDisposition state

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
    memoryServerCorrect connectionCorrect streamCorrect
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

end Grass.Spikes.WebServer
