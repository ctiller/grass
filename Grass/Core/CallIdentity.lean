import Grass.Core.Uid

/-!
# Synchronous call identities

The identity vocabulary for one synchronous call occurrence lives below the
memory and operation layers so both can name the same occurrence without an
import cycle.  Minting and freshness use `Grass.Core.FreshSupply`.
-/

namespace Grass.Op.CallProtocol

open Grass.Core

/-- Phantom tag for synchronous call-occurrence identities. -/
inductive CallTag : Type

/-- The generative identity of one synchronous call occurrence. -/
abbrev CallId := Uid CallTag

end Grass.Op.CallProtocol

