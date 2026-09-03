import Grass.Core.Uid
import Grass.Obligation.Delta

namespace Probe
open Grass.Core Grass.Obligation

noncomputable def peek {T : Type} (u : Uid T) : Nat :=
  Uid.rec (motive := fun _ => Nat) (fun i => i) u

example : peek ((FreshSupply.initial (Tag := Nat)).fresh.2.fresh.1) = 1 := by
  simp [peek, FreshSupply.fresh, FreshSupply.initial]

def forgedAuthority (p : ObligationProtocolId) : ProtocolAuthority p :=
  ⟨⟨"attacker.profile"⟩⟩

def forgedDischarge (p : ObligationProtocolId) (id : ObligationId) : LedgerDelta :=
  .discharge p (forgedAuthority p) id

end Probe
