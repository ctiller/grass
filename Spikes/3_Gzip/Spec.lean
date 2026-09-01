import Grass.Spec.Console
import Spikes.«3_Gzip».Resource

namespace Grass.Spikes.Gzip

inductive GzipOutcome
  | success
  | allocationFailure
  | inputFailure
  | outputFailure

def gzipContract {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : BehaviorContract resources :=
  Console.streamingGzipContract
    (resources := resources)
    (members := .one)
    (failureOutput := .constructionPrefix)

def gzipSpec {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : Specification resources :=
  Specification.ofRelational (gzipContract resources)
    |>.withOutcomes GzipOutcome
    |>.withProgress
        (.reactiveBetweenFrontiers
          |>.terminatesUnder [.stdinEventuallyEOF, .environmentResponsive])

theorem gzipSpecCorrect {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : MeetsAllSpecificationTheorems (gzipSpec resources) :=
  Console.streamingGzipContractCorrect resources GzipOutcome

theorem successfulTraceIffOneMemberRoundTrip
    {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) (input output : ByteArray) :
    SuccessfulConsoleTrace (gzipSpec resources) input output ↔
      Gzip.IsExactlyOneMember output ∧ Gzip.inflate output = .ok input :=
  Console.streamingGzipContract_success_iff resources GzipOutcome

def spec : Specification resources := gzipSpec resources

end Grass.Spikes.Gzip
