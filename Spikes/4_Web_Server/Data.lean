import Spikes.«4_Web_Server».Plan

namespace Grass.Spikes.WebServer

def routeBody : ByteArray :=
  #[0x47, 0x72, 0x61, 0x73, 0x73, 0x20, 0x77, 0x65, 0x62,
    0x20, 0x73, 0x65, 0x72, 0x76, 0x65, 0x72, 0x0a]

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
    worker_slots: zero (4 * workerSlotBytes)
    connection_states: zero (4 * connectionStateBytes)
    stream_states: zero (4 * resourcePolicy.maxConcurrentStreamsPerConnection * streamStateBytes)
  }
}

def serverImports : ImportTable := imports {
  KERNEL32.dll {
    CreateThread
    ResumeThread
    WaitForSingleObject
    CloseHandle
    Sleep
    SetConsoleCtrlHandler
    GetTickCount64
    ExitProcess
  }
  WS2_32.dll {
    WSAStartup
    WSASocketW
    bind
    listen
    ioctlsocket
    WSAPoll
    accept
    recv
    send
    WSAGetLastError
    closesocket
    WSACleanup
  }
}

end Grass.Spikes.WebServer
