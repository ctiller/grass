import Grass.Process.Network.Structural
import Grass.Semantics.SpecProcess

/-!
# Process presentation boundary

Refinement is the join of the independent Process and Semantics dependency
arms.  It reuses Process's one structural network declaration and instantiates
its protocol family with precious `SpecProcess` values.  It does not add
behavior, trace, or exactness fields to the Process-owned structure.

The selected-trace and exact-presentation records will live in this module as
well.  Their composition witness is intentionally not represented by an axiom
or a content-free proposition; its concrete carrier must be fixed before those
interfaces are exposed.
-/

namespace Grass.Refinement

universe u

/--
The Process-owned structural network instantiated at semantic protocols.

A protocol instance supplies one admitted protocol input.  The subtype retains
the admission proof needed by later trace-composition certificates rather than
letting a role claim an input outside its protocol's specified domain.
-/
abbrev ProcessPresentationNetwork :=
  Grass.Process.StructuralProcessNetwork SpecProcess.{u}
    (fun protocol => { input : protocol.Input // protocol.admits input })

end Grass.Refinement
