import Grass.Memory.Authority

/-!
# Minting identities for a batch of authority grants

This helper threads one explicit supply through a list. `id_not_issued` states
freshness relative to that starting supply; independent supplies are not compared.
-/

namespace Grass.Memory.GrantMint

open Grass.Core

/-- Pair each grant with a freshly minted identity, in list order. -/
def mint (supply : FreshSupply GrantTag) (grants : List AuthorityGrant) :
    List (GrantId × AuthorityGrant) × FreshSupply GrantTag :=
  match grants with
  | [] => ([], supply)
  | grant :: rest =>
      let issued := supply.fresh
      let tail := mint issued.2 rest
      ((issued.1, grant) :: tail.1, tail.2)

@[simp] theorem mint_nil (supply : FreshSupply GrantTag) :
    mint supply [] = ([], supply) := rfl

@[simp] theorem mint_cons (supply : FreshSupply GrantTag) (grant : AuthorityGrant)
    (rest : List AuthorityGrant) :
    mint supply (grant :: rest) =
      ((supply.fresh.1, grant) :: (mint supply.fresh.2 rest).1,
        (mint supply.fresh.2 rest).2) := rfl

/-- `map_snd_mint` states that minting preserves the grants and their order. -/
theorem map_snd_mint (supply : FreshSupply GrantTag) (grants : List AuthorityGrant) :
    (mint supply grants).1.map Prod.snd = grants := by
  induction grants generalizing supply with
  | nil => rfl
  | cons grant rest ih => simp [mint, ih]

/-- The returned supply is reached by exactly the sequence of fresh operations
performed by `mint`. -/
theorem supply_reachable (supply : FreshSupply GrantTag) (grants : List AuthorityGrant) :
    FreshSupply.Reachable supply (mint supply grants).2 := by
  induction grants generalizing supply with
  | nil => exact .refl supply
  | cons grant rest ih =>
      exact (FreshSupply.Reachable.mint (.refl supply)).trans (ih supply.fresh.2)

/-- Every output identity was fresh relative to the original supply. -/
theorem id_not_issued (supply : FreshSupply GrantTag) (grants : List AuthorityGrant) :
    ∀ entry ∈ (mint supply grants).1, ¬ supply.Issued entry.1 := by
  induction grants generalizing supply with
  | nil => simp [mint]
  | cons grant rest ih =>
      intro entry present
      simp only [mint_cons, List.mem_cons] at present
      rcases present with rfl | present
      · exact FreshSupply.fresh_not_issued supply
      · intro issued
        exact ih supply.fresh.2 entry present
          (issued.mono (FreshSupply.Reachable.mint (.refl supply)))

/-- Every output identity is issued by the resulting supply. -/
theorem id_issued (supply : FreshSupply GrantTag) (grants : List AuthorityGrant) :
    ∀ entry ∈ (mint supply grants).1, (mint supply grants).2.Issued entry.1 := by
  induction grants generalizing supply with
  | nil => simp [mint]
  | cons grant rest ih =>
      intro entry present
      simp only [mint_cons, List.mem_cons] at present
      rcases present with rfl | present
      · have issued : supply.fresh.2.Issued supply.fresh.1 :=
          (FreshSupply.issued_fresh supply supply.fresh.1).2 (.inr rfl)
        exact issued.mono (supply_reachable supply.fresh.2 rest)
      · exact ih supply.fresh.2 entry present

/-- A single threaded supply never assigns the same identity twice. -/
theorem ids_nodup (supply : FreshSupply GrantTag) (grants : List AuthorityGrant) :
    ((mint supply grants).1.map Prod.fst).Nodup := by
  induction grants generalizing supply with
  | nil => simp [mint]
  | cons grant rest ih =>
      simp only [mint_cons, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih supply.fresh.2⟩
      intro present
      rw [List.mem_map] at present
      obtain ⟨entry, entryPresent, equal⟩ := present
      have notIssued := id_not_issued supply.fresh.2 rest entry entryPresent
      have issued : supply.fresh.2.Issued supply.fresh.1 :=
        (FreshSupply.issued_fresh supply supply.fresh.1).2 (.inr rfl)
      exact notIssued (equal ▸ issued)

end Grass.Memory.GrantMint
