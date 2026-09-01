import Grass.Std.Protocol.Http2
import Grass.Spec.Resource

namespace Grass.Spikes.WebServer

def semanticBudget : Http2ServerSemanticBudget where
  maxActiveConnections := 4
  maxConcurrentStreamsPerConnection := 128
  maxHeaderListBytes := 16384
  hpackDecoderTableBytes := 4096
  hpackEncoderTableBytes := 0
  maxInboundFrameBytes := 16384
  maxContinuationBytes := 16384
  inboundConnectionWindow := 65535
  inboundStreamWindow := 65535
  outboundConnectionWindowCeiling := 2147483647
  outboundStreamWindowCeiling := 2147483647
  streamProgressDeadline := .seconds 5
  connectionIdleDeadline := .seconds 30

def resources : ServerResourceModel :=
  ServerResourceModel.http2 semanticBudget

def body : ByteArray := "Grass web server\n".toUTF8

def endpoint : TcpEndpoint := .ipv4Loopback 8080

def routes : Http2Routes :=
  .singleton { method := .GET, scheme := .http, authority := .any,
    path := "/".toASCII, response :=
      { status := 200, fields := [("content-type", "text/plain")], body } }

def behaviorPolicyFor {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : Http2ServerBehaviorPolicy :=
  Http2ServerBehaviorPolicy.fromCapturedResources resources where
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
    hpackDecoderTableBytes := WebServerResources.hpackDecoderTableBytes resources
    maxHeaderListBytes := WebServerResources.maxHeaderListBytes resources
    initialConnectionWindow := WebServerResources.inboundConnectionWindow resources
    initialStreamWindow := WebServerResources.inboundStreamWindow resources
    hpackEncoder := .anyConformingEncoding
    huffman := .acceptValidRejectInvalid

def protocolProfileFor {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : Http2.ServerProfile R :=
  Http2.ServerProfile.rfc9113CleartextPriorKnowledge
    (budget := Http2ServerSemanticBudget.fromResources resources)
    (behavior := behaviorPolicyFor resources)

def protocolPackageFor {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : Http2.Server.Package R :=
  Http2.Server.package resources (protocolProfileFor resources) routes

def webServerSuite {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : SpecificationSuite resources :=
  (protocolPackageFor resources).suite
    |>.atEndpoint endpoint

def webServerSpec {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (webServerSuite resources)
    |>.withProgress
      { service := .reactive
        acceptedConnection := .settlesUnder
          [.schedulerFair, .monotonicClockAdvances, .environmentResponsive]
        termination := .under
          [.shutdownEventuallyRequested, .schedulerFair,
           .monotonicClockAdvances, .environmentResponsive] }

theorem webServerSpecCorrect {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : MeetsAllSpecificationTheorems (webServerSpec resources) :=
  (protocolPackageFor resources).captureCorrectAtEndpoint endpoint

theorem clientObservableBehavior {R : Type}
    [ResourceModel R] [WebServerResources R] (resources : R) :
    ∀ trace, (webServerSpec resources).Accepts trace →
      (∀ exchange ∈ trace.completedExchanges,
        (exchange.request.method = .GET ∧ exchange.request.path = "/".toASCII →
          exchange.response.status = 200 ∧
          exchange.response.body = "Grass web server\n".toUTF8) ∧
        (exchange.request.method = .GET ∧ exchange.request.path ≠ "/".toASCII →
          exchange.response.status = 404 ∧ exchange.response.body = #[]) ∧
        (exchange.request.method ≠ .GET →
          exchange.outcome = .rejectedRequestMethod)) ∧
      trace.listenEndpoint = endpoint :=
  (protocolPackageFor resources).clientObservableCorrect endpoint

def spec : SpecProcess resources := webServerSpec resources

def protocolPackage : Http2.Server.Package resources :=
  protocolPackageFor resources

def behaviorPolicy : Http2ServerBehaviorPolicy := protocolPackage.profile.behavior

def capturedSemanticBudget : Http2ServerSemanticBudget :=
  Http2ServerSemanticBudget.fromCapturedSemantics spec.resourceSemantics

theorem capturedSemanticBudgetExact : capturedSemanticBudget = semanticBudget :=
  SpecProcess.capturedResourceConstructionExact spec

end Grass.Spikes.WebServer
