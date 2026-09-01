import Grass.Spec.Resource

namespace Grass.Spikes.WebServer

def resourcePolicy : MemoryServerResourcePolicy where
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
  maxQueuedControlFramesPerConnection := 32
  maxQueuedDataBytesPerConnection := 65535
  maxReceiveBytesPerConnection := 32768
  maxTransmitBytesPerConnection := 65535
  maxSocketDescriptors := 5
  maxThreadHandles := 4
  pollQuantum := .milliseconds 10
  streamProgressDeadline := .seconds 5
  connectionIdleDeadline := .seconds 30
  storage := .fixedAfterReady

def resources : ServerResourceModel :=
  ServerResourceModel.http2 resourcePolicy

end Grass.Spikes.WebServer
