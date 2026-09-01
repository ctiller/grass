import Grass.Std.Http2.X86
import Spikes.«4_Web_Server».Data

namespace Grass.Spikes.WebServer

def parseFrameHeaderMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.parseFrameHeader
    (maxFrameSize := 16384)

def consumeClientPrefaceMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.consumeClientPreface

def decodeFieldSectionMacro : VerifiedMacro platformPlan :=
  Grass.Std.Hpack.X86.decodeFieldSection
    (tableBytes := resourcePolicy.hpackDecoderTableBytes)
    (headerListBytes := resourcePolicy.maxHeaderListBytes)

def appendContinuationMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.appendContinuation
    (capacity := resourcePolicy.maxContinuationBytes)

def dispatchFrameMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.dispatchFrame protocolProfile

def requireInitialSettingsMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.requireInitialPeerSettings

def validateRequestFieldsMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.validateRequestFields routes

def applySettingsMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.applySettings serverSettings

def applyWindowUpdateMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.applyWindowUpdate

def transitionStreamMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.transitionStreamState

def enqueueControlMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.enqueueControlFrame
    resourcePolicy.maxQueuedControlFramesPerConnection

def enqueueResponseMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.enqueueStaticResponse
    successHeaderBlock routeBody

def enqueueNotFoundMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.enqueueStaticResponse notFoundHeaderBlock #[]

def enqueueErrorMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.enqueueScopedError

def debitInboundCreditMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.debitInboundFlowCredit

def releaseInboundDataMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.releaseDiscardedInboundData
    resourcePolicy.maxQueuedControlFramesPerConnection

def debitOutboundCreditMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.debitOutboundFlowCredit

def applyRstStreamMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.applyRstStream

def applyGoawayMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.applyGoaway

def acknowledgePingMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.acknowledgePing

def serializeSelectedFrameMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.serializeSelectedFrame

def commitSentPrefixMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.commitSentPrefix

def releaseClosedStreamsMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.releaseClosedStreams

def selectOutboundMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.selectFairOutboundFrame

def hasSendableOutboundMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.hasSendableOutboundFrame

def cancelExpiredStreamsMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.cancelExpiredStreams
    resourcePolicy.maxConcurrentStreamsPerConnection

def checkConnectionDeadlineMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.checkConnectionIdleDeadline
    resourcePolicy.connectionIdleDeadline

def initializeConnectionMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.initializeConnection resourcePolicy serverSettings

def receiveIntoRingMacro : VerifiedMacro platformPlan :=
  Grass.Std.Network.X86.receiveIntoBoundedRing resourcePolicy.maxReceiveBytesPerConnection

def pollConnectionMacro : VerifiedMacro platformPlan :=
  Grass.Std.Network.X86.pollConnection

def pollWritableMacro : VerifiedMacro platformPlan :=
  Grass.Std.Network.X86.pollWritable

def validateIgnoredPriorityMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.validateIgnoredPriority

def consumeUnknownPayloadMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.consumeUnknownPayload

def enqueueGoawayMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.beginGracefulShutdown

def shouldCloseDrainedMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.shouldCloseDrainedConnection

def releaseConnectionMacro : VerifiedMacro platformPlan :=
  Grass.Std.Http2.X86.releaseConnection

def serverMacros : MacroTable platformPlan := macros {
  h2_consume_preface => consumeClientPrefaceMacro
  h2_parse_frame_header => parseFrameHeaderMacro
  hpack_decode_field_section => decodeFieldSectionMacro
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
}

theorem serverMacrosTransparent :
    EveryMacroExpandsToExactRawInstructions serverMacros := by
  exact MacroTable.allTransparent serverMacros

theorem serverMacrosCancellationTransparent :
    EveryMacroExpansionPreservesCancellationMasksSafePointsAndCustody
      serverMacros := by
  exact MacroTable.allCancellationTransparent serverMacros

end Grass.Spikes.WebServer
