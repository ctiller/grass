import Grass.Process.Cancellation
import Spikes.«4_Web_Server».Process

namespace Grass.Spikes.WebServer

def serverCancellationPolicy :
    CancellationPolicy memoryServerProcess := cancellation_policy {
  atomic hpackSlice {
    process := Hpack.decodeSliceProcess protocolProfile
    bound := Hpack.decodeSliceStepBound
    commit := Hpack.commitCompletedSlice
    abandon := Hpack.returnLastCommitted
    privateWorkingState := Hpack.workingSlicePrivate
  }

  atomic sentPrefixCommit {
    process := Http2.commitSentPrefixProcess
    bound := Http2.commitSentPrefixStepBound
    prohibitCancellationBefore := Http2.ControlPoint.sentPrefixCommitted
  }

  boundedCall pollAccept {
    process := Std.Process.Network.pollAccept
    frontier := resourcePolicy.pollQuantum
  }

  boundedCall accept {
    process := Std.Process.Network.accept
    frontier := Std.Win32.Winsock.nonblockingAcceptBound
  }

  boundedCall pollReadable {
    process := Std.Process.Network.pollReadable
    frontier := resourcePolicy.pollQuantum
  }

  boundedCall receive {
    process := Std.Process.Network.receive
    frontier := Std.Win32.Winsock.nonblockingReceiveBound
  }

  boundedCall pollWritable {
    process := Std.Process.Network.pollWritable
    frontier := resourcePolicy.pollQuantum
  }

  boundedCall send {
    process := Std.Process.Network.send
    frontier := Std.Win32.Winsock.nonblockingSendBound
  }

  cancelPoint beforeAcceptPoll
  cancelPoint afterReadablePoll
  cancelPoint afterReceiveResult
  cancelPoint afterWritablePoll
  cancelPoint flowCreditWait
  cancelPoint completedFrame
  cancelPoint betweenHpackSlices
  cancelPoint goawayDrain
  cancelPoint rootShutdown

  route (.stream connection stream) .deadline => {
    at flowCreditWait =>
      enqueueRstWithoutDataCredit stream .cancel
    duringFrame =>
      finishCurrentFrameThenRst stream .cancel
    preserveSiblingStreams connection stream
    neverAddress (.hpackDecoder connection)
  }

  route (.connection connection) .shutdown => {
    stopNewStreams connection
    publishGoawayOnce connection
    freezeLastAdmittedStream connection
    drainUntil resourcePolicy.connectionDrainDeadline
    otherwise closeWithExactSuffixDisposition connection
  }

  route .server .shutdown => {
    stopAdmission
    cancelWorkersAtSafePoints
    preserveEveryLiveSocketUntilOwnedClose
    adoptOnlyDeclaredFailureObligations
  }

  requireEveryContinuingLoopCrossesCancelPoint
  requireEveryAtomicRegionTerminatesWithinItsBound
  requireTerminalDispositions [.normalDischarged, .failedWithDeclaredAdoption]
}

def serverCancellation : CancellationSummary memoryServerProcess := by
  elaborate_cancellation_policy serverCancellationPolicy

theorem serverCancellationCorrect :
    CancellationPolicyRealizes
      serverCancellationPolicy serverCancellation := by
  verify_cancellation_policy

theorem serverProcessPlanRealizes :
    ProcessPlanRealizes spec serverProcessPlan := by
  verify_process_plan
    using serverComposition
    using_processes
      memoryServerCorrect connectionCorrect streamCorrect frameParserCorrect
      hpackDecoderCorrect connectionWriterCorrect
    using_cancellation serverCancellationCorrect

end Grass.Spikes.WebServer
