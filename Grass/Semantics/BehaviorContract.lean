import Grass.Semantics.BehaviorModel
import Grass.Resource.Algebra
import Grass.Core.Demand

namespace Grass

/-- A statement and its dependency facets, computed by the selected language. -/
structure AuthoredDemand where
  kind : RequirementKind
  statement : Prop
  dependencies : List StableId

/-- A selected relational language interprets captured syntax and resources.
The `denotation` and `demands` functions consume the same snapshot. -/
structure BehaviorLanguage (R : Type) (resourceModel : Resource.ResourceModel R) where
  Syntax : Type 1
  Snapshot : R → Type
  Input : Syntax → Type
  Outcome : Syntax → Type
  Interpretation : Syntax → Type
  admits : (authored : Syntax) → Input authored → Prop
  denotation : (resources : R) → (authored : Syntax) → Snapshot resources →
    Interpretation authored → Input authored → BehaviorModel.{0, 0, 0, 0} (Outcome authored)
  demands : (resources : R) → (authored : Syntax) → Snapshot resources → List AuthoredDemand

/-- Construction captures one authored value and one resource snapshot. -/
structure BehaviorContract {R : Type} [resourceModel : Resource.ResourceModel R]
    (resources : R) where
  language : BehaviorLanguage R resourceModel
  authored : language.Syntax
  snapshot : language.Snapshot resources

namespace BehaviorContract
variable {R : Type} [Resource.ResourceModel R] {resources : R}
abbrev Input (contract : BehaviorContract resources) := contract.language.Input contract.authored
abbrev Outcome (contract : BehaviorContract resources) := contract.language.Outcome contract.authored
abbrev Interpretation (contract : BehaviorContract resources) :=
  contract.language.Interpretation contract.authored
def admits (contract : BehaviorContract resources) : contract.Input → Prop :=
  contract.language.admits contract.authored
def denotation (contract : BehaviorContract resources) (interpretation : contract.Interpretation)
    (input : contract.Input) : BehaviorModel.{0, 0, 0, 0} contract.Outcome :=
  contract.language.denotation resources contract.authored contract.snapshot interpretation input
def demands (contract : BehaviorContract resources) : List AuthoredDemand :=
  contract.language.demands resources contract.authored contract.snapshot
end BehaviorContract
end Grass
