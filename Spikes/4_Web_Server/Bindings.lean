import Spikes.«4_Web_Server».SourceClosure

namespace Grass.Spikes.WebServer

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

theorem workerCreationFailureNeverPublishesReady (index : Fin 4) :
    CreateThreadFailsAt index serverExpandedSource ⟹
      Always (ReadyFlag = 0) ∧
      EmitsNoProtocolBytes ∧
      EventuallyJoinsAndClosesCreatedPrefix index ∧
      TerminatesWithFailure :=
  verify_startup_failure_path index

theorem workerResumeFailureNeverPublishesReady
    (created : Nat) (created_le : created ≤ 4) (index : Fin created) :
    ResumeThreadFailsAt created index serverExpandedSource ⟹
      Always (ReadyFlag = 0) ∧
      EmitsNoProtocolBytes ∧
      TerminatesByDeclaredFailedAdoption :=
  verify_resume_failure_path created created_le index

def serverCancellationBlockMap :
    CancellationCfgMap serverExpandedSource serverCancellation :=
  cancellation_cfg_total {
    entry => uncancellable FixedPool.Segment.entrySetup
    create_workers => uncancellable FixedPool.Segment.createWorker
    resume_workers => uncancellable FixedPool.Segment.beginSuccessfulResume
    resume_loop => uncancellable FixedPool.Segment.successfulResume
    publish_ready => uncancellable FixedPool.Segment.publishReady
    service_loop => observe FixedPool.CancelPoint.rootShutdownObservation
    startup_partial_workers => uncancellable FixedPool.Segment.latchStartupFailure
    resume_failure_workers => uncancellable FixedPool.Segment.failureResumeOnly
    join_workers => uncancellable FixedPool.Segment.joinWorker
    unregister_handler => uncancellable FixedPool.Segment.unregisterHandler
    close_listener => uncancellable FixedPool.Segment.closeListener
    cleanup_wsa => uncancellable FixedPool.Segment.cleanupWinsock
    finish_status => terminalChoice
      FixedPool.Terminal.normalDischarged
      FixedPool.Terminal.failedAdoption
    startup_failure_socket => uncancellable FixedPool.Segment.startupSocketCleanup
    startup_failure_wsa => uncancellable FixedPool.Segment.startupWinsockCleanup
    exit_failure_no_wsa => terminal FixedPool.Terminal.failedAdoption
    fatal_exit => terminal FixedPool.Terminal.failedAdoption
    console_handler => requestPublisher FixedPool.CancellationSource.consoleControl
    worker_entry => uncancellable FixedPool.Segment.workerEntry
    worker_gate => observe FixedPool.CancelPoint.workerGateObservation
    accept_wait => observe FixedPool.CancelPoint.acceptLoopObservation
    accepted_connection => uncancellable FixedPool.Segment.acceptedInitialization
    accepted_mode_failure => uncancellable FixedPool.Segment.acceptedFailureCleanup
    preface_loop => observe Http2.CancelPoint.prefaceObservation
    connection_schedule => observe Http2.CancelPoint.schedulerObservation
    connection_deadlines => uncancellable Http2.Segment.deadlineAndRelease
    receive_frames => uncancellable Http2.Segment.boundedReceive
    receive_result_observation => observe Http2.CancelPoint.receiveResultObservation
    frame_parse_loop => safeState Http2.SafePoint.frameBoundary
    frame_headers => uncancellable Http2.Segment.streamTransition
    begin_continuation => uncancellable Http2.Segment.beginContinuation
    frame_continuation => uncancellable Http2.Segment.continuationAppend
    decode_fields => expands hpackDecoderCancellation
    enqueue_success => uncancellable Http2.Segment.enqueueSuccess
    enqueue_not_found => uncancellable Http2.Segment.enqueueNotFound
    frame_data => uncancellable Http2.Segment.flowCreditTransition
    frame_settings => uncancellable Http2.Segment.settingsTransition
    frame_ping => uncancellable Http2.Segment.pingTransition
    frame_goaway => uncancellable Http2.Segment.goawayTransition
    frame_rst_stream => uncancellable Http2.Segment.resetTransition
    frame_window_update => uncancellable Http2.Segment.windowTransition
    frame_ignore_priority => uncancellable Http2.Segment.ignorePriority
    frame_ignore_unknown => uncancellable Http2.Segment.ignoreUnknown
    send_selected_frame => uncancellable Http2.Segment.selectDebitSerialize
    send_suffix_loop => uncancellable Http2.Segment.boundedWritablePoll
    send_readiness_observation => observe Http2.CancelPoint.writerReadinessObservation
    send_positive => uncancellable Http2.Segment.commitSentPrefix
    stream_refused => uncancellable Http2.Segment.classifyRefused
    stream_protocol_error => uncancellable Http2.Segment.classifyStreamProtocolError
    stream_flow_error => uncancellable Http2.Segment.classifyStreamFlowError
    enqueue_stream_error => uncancellable Http2.Segment.enqueueReset
    connection_compression_error => uncancellable Http2.Segment.classifyCompressionError
    connection_flow_error => uncancellable Http2.Segment.classifyConnectionFlowError
    connection_protocol_error => uncancellable Http2.Segment.classifyConnectionProtocolError
    connection_internal_error => uncancellable Http2.Segment.classifyInternalError
    enqueue_connection_error => uncancellable Http2.Segment.enqueueGoaway
    connection_shutdown => uncancellable Http2.Segment.beginShutdown
    connection_draining => safeState Http2.SafePoint.drainBoundary
    connection_goaway_failure => uncancellable Http2.Segment.markTeardownSuffix
    connection_peer_close => uncancellable Http2.Segment.classifyPeerClose
    connection_io_error => uncancellable Http2.Segment.classifyIoError
    connection_close => uncancellable Http2.Segment.closeAndReleaseConnection
    connection_closed_boundary => observe Http2.CancelPoint.connectionClosedObservation
    worker_return => terminal FixedPool.Terminal.workerDischarged
    edges => classifyEveryExpandedEdgeByInstructionSemantics
  }

theorem serverCfgCancellationRefines :
    CancellationCfgRefines
      serverExpandedSource serverCancellationBlockMap serverCancellation := by
  verify_cancellation_cfg

theorem frameBoundaryMapsToSafePoint :
    serverCancellationBlockMap.atLabel `frame_parse_loop =
      .safeState Http2.SafePoint.frameBoundary :=
  rfl

theorem partialSendExpansionRestoresSuffixBeforeCancel :
    CancellationCfgPathSatisfies serverCancellationBlockMap
      `send_suffix_loop
      [.boundedUncancellableCall, .cancellationObservation,
       .boundedUncancellableCall, .uncancellableCommit,
       .frameBoundaryObservationOrExactTeardown] :=
  serverCfgCancellationRefines.path _

theorem blockedReadinessReturnsToRealCancellationObservation :
    CancellationCfgPathSatisfies serverCancellationBlockMap
      `receive_frames
      [.boundedUncancellableCall, .cancellationObservation] :=
  serverCfgCancellationRefines.path _

theorem connectionCloseMapsToDischargedSafeBoundary :
    serverCancellationBlockMap.atLabel `connection_closed_boundary =
      .observe Http2.CancelPoint.connectionClosedObservation :=
  rfl

theorem finishStatusMapsBothTerminalClasses :
    serverCancellationBlockMap.atLabel `finish_status =
      .terminalChoice
        FixedPool.Terminal.normalDischarged
        FixedPool.Terminal.failedAdoption :=
  rfl

theorem noSafePointAtMidHpackMutation :
    ¬ serverCancellationBlockMap.isSafe
      (serverExpandedSource.expandedControlPoint
        `hpack_decode_field_section `mid_dynamic_table_mutation) :=
  serverCfgCancellationRefines.noCounterfeitSafePoint _

theorem noSafePointAfterSendBeforeCommit :
    ¬ serverCancellationBlockMap.isSafe
      (serverExpandedSource.controlPoint
        `send_suffix_loop `send_returned_before_commit) :=
  serverCfgCancellationRefines.noCounterfeitSafePoint _

theorem callbackCannotCounterfeitStreamCancelPoint :
    EveryCallbackInterleavingPreservesCancellationMask
      serverExpandedSource serverCancellationBlockMap :=
  serverCfgCancellationRefines.callbackMasks

theorem everyExpandedBlockAndEdgeIsClassified :
    TotalCancellationCfgClassification
      serverExpandedSource serverCancellationBlockMap :=
  serverCfgCancellationRefines.total

theorem noReachableBlockUsesFallbackClassification :
    ∀ block ∈ serverExpandedSource.reachableBlocks,
      serverCancellationBlockMap.classification block ≠ .unmapped :=
  serverCfgCancellationRefines.noUnmappedReachableBlock

theorem untypedInteriorInstructionCannotBeCancellationSafe
    (point : serverExpandedSource.ControlPoint)
    (untyped : ¬ HasCancellationBoundaryContract point) :
    ¬ serverCancellationBlockMap.isSafe point :=
  serverCfgCancellationRefines.onlyTypedBoundaries point untyped

end Grass.Spikes.WebServer
