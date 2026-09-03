import Grass.Core.Uid
namespace Probe
open Grass.Core

noncomputable def issuedCount {T : Type} (s : FreshSupply T) : Nat :=
  FreshSupply.rec (motive := fun _ => Nat) (fun n => n) s

def supplyAt (T : Type) : Nat → FreshSupply T
  | 0 => .initial
  | n + 1 => (supplyAt T n).fresh.2

noncomputable def rewind {T : Type} (s : FreshSupply T) : FreshSupply T :=
  supplyAt T (issuedCount s - 1)

/-- `issuedCount` really reads the counter. -/
theorem count_supplyAt (T : Type) : ∀ n, issuedCount (supplyAt T n) = n
  | 0 => rfl
  | n + 1 => by simp [supplyAt, FreshSupply.fresh, issuedCount] at *; omega

/-- Rewinding a supply re-issues an identity it had already minted. -/
theorem reissue (T : Type) :
    (rewind (supplyAt T 4)).fresh.1 = (supplyAt T 3).fresh.1 := by
  simp [rewind, count_supplyAt]

/-- And that identity was already `Issued` by the original supply. -/
theorem stale_is_live (T : Type) :
    (supplyAt T 4).Issued (rewind (supplyAt T 4)).fresh.1 := by
  rw [reissue]
  simp [FreshSupply.Issued, FreshSupply.fresh, count_supplyAt (T := T) 3,
    show (supplyAt T 3).fresh.1 = (supplyAt T 3).fresh.1 from rfl]
  sorry

end Probe
