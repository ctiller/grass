import Grass.Spec.Console
import Spikes.«2_Sort».Resource

namespace Grass.Spikes.Sort

def format : ByteLineFormat := .lfDelimited (.normalizeFinal true)

def order : ByteStringOrder := .lexicographicUnsigned

inductive SortOutcome
  | success
  | allocationFailure
  | inputFailure
  | outputFailure

structure Occurrence where
  ordinal : Nat
  value : ByteArray

def Occurrence.le (left right : Occurrence) : Prop :=
  order.le left.value right.value

def stableSorted (input output : Vec Occurrence) : Prop :=
  output.Permutation input ∧
  output.Pairwise Occurrence.le ∧
  ∀ i j, i < j -> input[i].value = input[j].value ->
    (output.findIdx? input[i]).get! < (output.findIdx? input[j]).get!

def sortContract {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : BehaviorContract resources :=
  Console.stableLineSortContract
    (resources := resources)
    (format := format)
    (order := order)
    (outcomes := SortOutcome)

def sortSpec {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : Specification resources :=
  Specification.ofRelational (sortContract resources)
    |>.onResourceExhaustion .allocationFailure
    |>.withLiveness
        (.terminatesUnder [.stdinEventuallyEOF, .environmentResponsive])

theorem sortSpecCorrect {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : MeetsAllSpecificationTheorems (sortSpec resources) :=
  Console.stableLineSortContractCorrect resources format order SortOutcome

theorem successfulTraceIffStableSorted
    {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) (input output : ByteArray) :
    SuccessfulConsoleTrace (sortSpec resources) input output ↔
      StableFormattedOccurrenceOutput format input output stableSorted :=
  Console.stableLineSortContract_success_iff
    resources format order SortOutcome

def spec : Specification resources := sortSpec resources

end Grass.Spikes.Sort
