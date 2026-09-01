import Grass.Std.Http2.Model
import Grass.Std.Hpack.Model
import Spikes.«4_Web_Server».Spec

namespace Grass.Spikes.WebServer

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

theorem hpackIntegerWriterRoundTrip (prefix : Fin 9) (n : Nat) :
    Hpack.Integer.parse prefix (Hpack.Integer.write prefix n) = .ok n :=
  Hpack.Integer.parse_write prefix n

theorem hpackStringWriterRoundTrip (value : ByteArray) :
    Hpack.StringLiteral.parse (Hpack.StringLiteral.writePlain value) = .ok value :=
  Hpack.StringLiteral.parse_writePlain value

theorem hpackDecoderConforms (state : Hpack.DecoderState protocolProfile)
    (block : ByteArray) :
    Hpack.decode state block = .error ∨
    ∃ next fields,
      Hpack.decode state block = .ok (next, fields) ∧
      Hpack.Rfc7541Transition state block next fields ∧
      next.dynamicTable.bytes ≤ capturedResourcePolicy.hpackDecoderTableBytes ∧
      fields.byteSize ≤ capturedResourcePolicy.maxHeaderListBytes :=
  Hpack.decode_conforms state block

theorem huffmanDecoderExact (encoded : ByteArray) :
    Hpack.Huffman.decode encoded = .error ∨
    ∃ decoded,
      Hpack.Huffman.decode encoded = .ok decoded ∧
      Hpack.Huffman.ValidEncoding encoded decoded :=
  Hpack.Huffman.decode_exact encoded

theorem connectionModelCoversClaimedProfile :
    Http2.CoversFrameKinds connectionModel
      [.data, .headers, .priority, .rstStream, .settings, .pushPromise,
       .ping, .goaway, .windowUpdate, .continuation, .unknown] ∧
    Http2.CoversStreamStates connectionModel
      [.idle, .open, .halfClosedLocal, .halfClosedRemote, .closed] ∧
    Http2.CoversErrorScopes connectionModel
      [.connection, .stream, .ignored] :=
  Http2.ConnectionModel.profileComplete protocolProfile behaviorPolicy routes

theorem flowCreditsConserved :
    Http2.ConnectionAndStreamFlowCreditInvariant connectionModel :=
  Http2.ConnectionModel.flowCreditsConserved connectionModel

theorem hpackOrderIsConnectionOrder :
    Http2.HpackTransitionsFollowConnectionFrameOrder connectionModel :=
  Http2.ConnectionModel.hpackConnectionOrdered connectionModel

end Grass.Spikes.WebServer
