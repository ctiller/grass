import Grass.Spec.Http2
import Spikes.«4_Web_Server».Resource

namespace Grass.Spikes.WebServer

def body : ByteArray := "Grass web server\n".toUTF8

def routes : Http2Routes :=
  .singleton { method := .GET, scheme := .http, authority := .any,
    path := "/".toASCII, response :=
      { status := 200, fields := [("content-type", "text/plain")], body } }

def behaviorPolicy : Http2ServerBehaviorPolicy where
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
  hpack :=
    { decoder := .rfc7541
      encoder := .literalWithoutIndexing
      dynamicTableBytes := resourcePolicy.hpackDecoderTableBytes
      huffman := .acceptValidRejectInvalid }

inductive ServerRoleSchema
  | listener
  | connection
  | stream

def ServerRoleSchema.Instance : ServerRoleSchema -> Type
  | .listener => Unit
  | .connection => ConnectionId
  | .stream => ConnectionId × Http2StreamId

def connectionSession {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) (id : ConnectionId) : SpecProcess resources :=
  Http2.abstractConnectionSession resources routes behaviorPolicy id

def streamSession {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) (connection : ConnectionId) (stream : Http2StreamId) :
    SpecProcess resources :=
  Http2.abstractRequestStream resources routes behaviorPolicy connection stream

def abstractServer {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : AbstractSpecificationProcessNetwork resources :=
  Http2.abstractMemoryServer
    (roleSchema := ServerRoleSchema)
    (instances := ServerRoleSchema.Instance)
    (routes := routes)
    (connection := connectionSession resources)
    (stream := streamSession resources)
    (admission := WebServerResources.connectionCapacity resources)
    (custody := .linearPerConnectionAndStream)

def webServerSpec {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : Specification resources :=
  Specification.ofProcesses (abstractServer resources)
    |>.withProgress
      { service := .reactive
        acceptedConnection := .settlesUnder
          [.schedulerFair, .monotonicClockAdvances, .environmentResponsive]
        termination := .under
          [.shutdownEventuallyRequested, .schedulerFair,
           .monotonicClockAdvances, .environmentResponsive] }

theorem webServerSpecCorrect {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : MeetsAllSpecificationTheorems (webServerSpec resources) :=
  Http2.abstractMemoryServerCorrect resources routes behaviorPolicy

def spec : Specification resources := webServerSpec resources

end Grass.Spikes.WebServer
