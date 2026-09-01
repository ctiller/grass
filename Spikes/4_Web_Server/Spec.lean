import Grass.Spec.Http2
import Grass.Spec.Grammar
import Spikes.«4_Web_Server».Resource

namespace Grass.Spikes.WebServer

def body : ByteArray := "Grass web server\n".toUTF8

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

def frameFormat : Format Http2.Frame :=
  Http2.frameFormat

def hpackFieldSectionFormat : Format Http2.HeaderList :=
  Hpack.fieldSectionFormat

def frameParserRequirement {R : Type} [ResourceModel R]
    (resources : R) : ProcessRequirement resources :=
  Format.parserRequirement frameFormat

def hpackParserRequirement {R : Type} [ResourceModel R]
    (resources : R) : ProcessRequirement resources :=
  Format.parserRequirement hpackFieldSectionFormat

def webServerSuite {R : Type} [ResourceModel R] [WebServerResources R]
    (resources : R) : SpecificationSuite resources :=
  Http2.memoryServerSuite
    resources routes (behaviorPolicyFor resources)
    (frameParserRequirement resources) (hpackParserRequirement resources)

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
  Http2.memoryServerSuiteCaptureCorrect
    resources routes (behaviorPolicyFor resources)
    (frameParserRequirement resources) (hpackParserRequirement resources)

def spec : SpecProcess resources := webServerSpec resources

def behaviorPolicy : Http2ServerBehaviorPolicy := behaviorPolicyFor resources

def capturedResourcePolicy : MemoryServerResourcePolicy :=
  MemoryServerResourcePolicy.fromCapturedSemantics spec.resourceSemantics

theorem capturedResourcePolicyExact : capturedResourcePolicy = resourcePolicy :=
  SpecProcess.capturedResourceConstructionExact spec

end Grass.Spikes.WebServer
