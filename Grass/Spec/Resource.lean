import Grass.Resource.Algebra
import Grass.Resource.Axis
import Grass.Spec.Root

/-!
# Specification-authoring facade: resources and the authoring root

A thin re-export module. The resource algebra lives in `Grass/Resource/*`; the
resource-indexed authoring root (`SpecProcess`, `BehaviorContract`,
`MeetsAllSpecificationTheorems`, `LivenessDemand`) lives in
`Grass/Spec/Root.lean`. Every identifier below is already declared directly in
namespace `Grass` except the resource-algebra vocabulary, which this module
aliases into `Grass` so a spike's `namespace Grass.Spikes.*` resolves it
unqualified without depending on `Grass.Resource`'s internal layout.
-/

namespace Grass

export Resource (ResourceModel ResourceAlgebra ResourceAxisName HasResourceAxis
  HasResourceLimit ResourceLimit ResourceExhaustionPolicy ResourceLifecyclePolicy)

end Grass
