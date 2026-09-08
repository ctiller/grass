import Grass.Spec.Console
import Grass.Spec.Grammar
import Grass.Spec.Resource

namespace Grass.Spikes.Sort

def resources : ConsoleBufferResourceModel :=
  ConsoleBufferResourceModel.untilMemoryExhaustion
    (onExhaustion := .terminateWithNoOutput)
    (capacity := .noArtificialLimit)

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
  ∀ (i j : Nat) (hi : i < input.length) (hj : j < input.length),
    (input.get i hi).value = (input.get j hj).value ->
    (input.get i hi).ordinal < (input.get j hj).ordinal ->
    ∀ p q, output.idxOf? (input.get i hi) = some p ->
           output.idxOf? (input.get j hj) = some q ->
           p < q

def lineStreamFormat : Format (Vec ByteArray) :=
  Console.byteLineStreamFormat format

def lineParserRequirement {R : Type} [ResourceModel R]
    (resources : R) : ProcessRequirement resources :=
  Format.parserRequirement lineStreamFormat

def sortSuite {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : SpecificationSuite resources :=
  Console.stableLineSortSuite
    (resources := resources)
    (format := format)
    (order := order)
    (outcomes := SortOutcome)
    (parser := lineParserRequirement resources)

def sortSpec {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (sortSuite resources)
    |>.onResourceExhaustion .allocationFailure
    |>.withLiveness
        (.terminatesUnder [.stdinEventuallyEOF, .environmentResponsive])

theorem sortSpecCorrect {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : MeetsAllSpecificationTheorems (sortSpec resources) :=
  Console.stableLineSortSuiteCaptureCorrect resources format order SortOutcome
    (lineParserRequirement resources)

theorem successfulTraceIffStableSorted
    {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) (input output : ByteArray) :
    SuccessfulConsoleTrace (sortSpec resources) input output ↔
      StableFormattedOccurrenceOutput format input output stableSorted :=
  Console.stableLineSortContract_success_iff
    resources format order SortOutcome

def spec : SpecProcess resources := sortSpec resources

end Grass.Spikes.Sort
