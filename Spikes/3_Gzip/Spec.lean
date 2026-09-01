import Grass.Spec.Console
import Grass.Spec.Grammar
import Grass.Spec.Resource

namespace Grass.Spikes.Gzip

def resources : StreamingResourceModel :=
  StreamingResourceModel.console
    |>.withResidentMemory .boundedIndependentOfInputLength

inductive GzipOutcome
  | success
  | allocationFailure
  | inputFailure
  | outputFailure

def outcomePolicy : StreamingFilterOutcomePolicy GzipOutcome where
  success := .success
  allocationFailure := .allocationFailure
  stdinUnavailable := .inputFailure
  readFailed := .inputFailure
  stdoutUnavailable := .outputFailure
  writeFailed := .outputFailure
  noProgress := .outputFailure

def gzipMemberFormat : Format Gzip.Member :=
  Gzip.memberFormat

def gzipSuite {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : SpecificationSuite resources :=
  Console.streamingGzipSuite
    (resources := resources)
    (members := .one)
    (outputFormat := gzipMemberFormat)
    (outcomes := outcomePolicy)
    (failureOutput := .constructionPrefix)

def gzipSpec {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (gzipSuite resources)
    |>.withOutcomes GzipOutcome
    |>.withProgress
        (.reactiveBetweenFrontiers
          |>.terminatesUnder [.stdinEventuallyEOF, .environmentResponsive])

theorem gzipSpecCorrect {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : MeetsAllSpecificationTheorems (gzipSpec resources) :=
  Console.streamingGzipSuiteCaptureCorrect
    resources outcomePolicy gzipMemberFormat

theorem successfulTraceIffOneMemberRoundTrip
    {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) (input output : ByteArray) :
    SuccessfulConsoleTrace (gzipSpec resources) input output ↔
      Gzip.IsExactlyOneMember output ∧ Gzip.inflate output = .ok input :=
  Console.streamingGzipContract_success_iff resources GzipOutcome
    outcomePolicy

def spec : SpecProcess resources := gzipSpec resources

end Grass.Spikes.Gzip
