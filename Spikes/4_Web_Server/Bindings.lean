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
    AssemblyNeverAllocatesAfterReady serverExpandedSource resourcePolicy := by
  verify_asm_resource_calls

def serverCancellationBlockMap :
    CancellationCfgMap serverExpandedSource serverCancellation :=
  cancellation_cfg_map {
    worker_gate => interruptible Std.Win32.Sleep.initializationGate
    accept_wait => interruptible Std.Win32.Winsock.pollAndAccept
    preface_loop => cancelpoint Http2.SafePoint.prefaceBoundary
    connection_schedule => cancelpoint Http2.SafePoint.schedulerBoundary
    receive_frames => interruptible Std.Win32.Winsock.pollAndReceive
    frame_parse_loop => cancelpoint Http2.SafePoint.frameBoundary
    frame_headers => uncancellable Http2.Segment.streamTransition
    frame_continuation => uncancellable Http2.Segment.continuationAppend
    decode_fields => expands hpackDecoderCancellation
    frame_data => uncancellable Http2.Segment.flowCreditTransition
    frame_settings => uncancellable Http2.Segment.settingsTransition
    frame_ping => uncancellable Http2.Segment.pingTransition
    frame_goaway => uncancellable Http2.Segment.goawayTransition
    frame_rst_stream => uncancellable Http2.Segment.resetTransition
    frame_window_update => uncancellable Http2.Segment.windowTransition
    send_selected_frame => uncancellable Http2.Segment.selectDebitSerialize
    send_suffix_loop => expands partialSendCancellation
    enqueue_stream_error => uncancellable Http2.Segment.enqueueReset
    enqueue_connection_error => uncancellable Http2.Segment.enqueueGoaway
    connection_draining => cancelpoint Http2.SafePoint.drainBoundary
    connection_close => uncancellable Http2.Segment.closeAndReleaseConnection
    connection_closed_boundary => cancelpoint Http2.SafePoint.connectionCustodyClosed
    worker_return => terminal FixedPool.Terminal.workerDischarged
    startup_failure_socket => uncancellable FixedPool.Segment.startupCleanup
    startup_failure_wsa => uncancellable FixedPool.Segment.winsockCleanup
    exit_failure_no_wsa => terminal FixedPool.Terminal.failedAdoption
    finish_status => terminalChoice
      FixedPool.Terminal.normalDischarged
      FixedPool.Terminal.failedAdoption
    fatal_exit => terminal FixedPool.Terminal.failedAdoption
  }

theorem serverCfgCancellationRefines :
    CancellationCfgRefines
      serverExpandedSource serverCancellationBlockMap serverCancellation := by
  verify_cancellation_cfg

theorem frameBoundaryMapsToSafePoint :
    serverCancellationBlockMap.atLabel `frame_parse_loop =
      .cancelPoint Http2.SafePoint.frameBoundary :=
  rfl

theorem partialSendExpansionRestoresSuffixBeforeCancel :
    CancellationCfgPathSatisfies serverCancellationBlockMap
      `send_suffix_loop
      [.interruptibleCall, .uncancellableCommit, .cancelPoint] :=
  serverCfgCancellationRefines.path _

theorem blockedReadinessMapsToInterruptibleProvider :
    CancellationCfgPathSatisfies serverCancellationBlockMap
      `receive_frames [.interruptibleCall] :=
  serverCfgCancellationRefines.path _

theorem connectionCloseMapsToDischargedSafeBoundary :
    serverCancellationBlockMap.atLabel `connection_closed_boundary =
      .cancelPoint Http2.SafePoint.connectionCustodyClosed :=
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

theorem untypedInteriorInstructionCannotBeCancellationSafe
    (point : serverExpandedSource.ControlPoint)
    (untyped : ¬ HasCancellationBoundaryContract point) :
    ¬ serverCancellationBlockMap.isSafe point :=
  serverCfgCancellationRefines.onlyTypedBoundaries point untyped

end Grass.Spikes.WebServer
