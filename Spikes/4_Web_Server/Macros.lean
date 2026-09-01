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

abbrev LocalFragmentBody
    (entry : BlockContract) (exits : FragmentExitFamily entry) :=
  X86.ClosedVerifiedFragmentBody entry exits

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

def normalizeHeadersPayloadBody :
    LocalFragmentBody Http2.X86.Contract.normalizeHeadersPayloadEntry
      Http2.X86.Contract.normalizeHeadersPayloadExit := x86_fragment_body {
  name := `normalizeHeadersPayload
  state := connection.currentPayload, connection.currentPayloadLength
  algorithm := requireFrameType headers
    |> ifFlag padded {
      requirePayloadLengthAtLeast 1
      readPadLength
      requirePaddingFitsPayload
      removePadLengthAndTrailingPadding
    }
    |> ifFlag priority {
      requirePayloadLengthAtLeast 5
      requirePriorityDependencyNotCurrentStream
      removePriorityPrefix
    }
    |> publishExactHeaderBlockSlice
}

def normalizeDataPayloadBody :
    LocalFragmentBody Http2.X86.Contract.normalizeDataPayloadEntry
      Http2.X86.Contract.normalizeDataPayloadExit := x86_fragment_body {
  name := `normalizeDataPayload
  state := connection.currentPayload, connection.currentPayloadLength,
    connection.currentFlowControlledLength
  algorithm := requireFrameType data
    |> snapshotFullPayloadLengthForFlowCredit
    |> ifFlag padded {
      requirePayloadLengthAtLeast 1
      readPadLength
      requirePaddingFitsPayload
      removePadLengthAndTrailingPadding
    }
    |> publishExactDataSlice
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

def serverMacros : MacroTable platformPlan := macros {
  h2_consume_preface => consumePrefaceBody
  h2_parse_frame_header => parseFrameHeaderBody 16384
  hpack_decode_field_section =>
    hpackFieldSectionBody
      resourcePolicy.hpackDecoderTableBytes
      resourcePolicy.maxHeaderListBytes
  h2_normalize_headers_payload => normalizeHeadersPayloadBody
  h2_normalize_data_payload => normalizeDataPayloadBody
  h2_begin_header_block =>
    beginHeaderBlockBody resourcePolicy.maxContinuationBytes
  h2_append_continuation =>
    continuationBody resourcePolicy.maxContinuationBytes
  h2_dispatch_frame => dispatchBody protocolProfile
  h2_require_initial_settings => initialSettingsBody
  h2_validate_request_fields => requestFieldsBody
  h2_apply_settings => settingsBody serverSettings
  h2_apply_window_update => windowUpdateBody
  h2_transition_stream => streamTransitionBody
  h2_enqueue_control =>
    boundedQueueBody .control resourcePolicy.maxQueuedControlFramesPerConnection
  h2_enqueue_response => staticResponseBody successHeaderBlock routeBody
  h2_enqueue_not_found => staticResponseBody notFoundHeaderBlock #[]
  h2_enqueue_error => scopedErrorBody
  h2_debit_inbound_credit => inboundCreditBody
  h2_release_inbound_data => releaseInboundBody
  h2_debit_outbound_credit => outboundCreditBody
  h2_apply_rst_stream => rstBody
  h2_apply_goaway => peerGoawayBody
  h2_ack_ping => pingBody
  h2_select_outbound => outboundSelectionBody
  h2_has_sendable_outbound => hasOutboundBody
  h2_serialize_selected_frame => serializeFrameBody
  h2_commit_sent_prefix => commitPrefixBody
  h2_release_closed_streams => releaseStreamsBody
  h2_cancel_expired_streams =>
    cancelExpiredBody resourcePolicy.maxConcurrentStreamsPerConnection
  h2_check_connection_deadline =>
    connectionDeadlineBody resourcePolicy.connectionIdleDeadline
  h2_initialize_connection_state => initializeConnectionBody
  receive_into_ring =>
    receiveRingBody resourcePolicy.maxReceiveBytesPerConnection
  connection_poll => pollReadableBody
  poll_connection_writable => pollWritableBody
  h2_validate_ignored_priority => ignoredPriorityBody
  h2_consume_unknown_payload => unknownPayloadBody
  h2_enqueue_goaway => localGoawayBody
  h2_should_close_drained => drainedBody
  h2_release_connection_state => releaseConnectionBody
  h2_mark_exact_teardown_suffix_disposition => teardownSuffixBody
  h2_observe_writer_cancellation => writerObservationBody
}

end Grass.Spikes.WebServer
