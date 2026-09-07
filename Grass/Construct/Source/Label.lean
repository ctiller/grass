import Grass.Core.Uid
import Grass.CFG.Contract

/-!
# Hygienic authored labels and alpha-normalization

Macro-local labels use opaque generative identities rather than `BlockId`.
`LabelSupply.mint` threads the monotone supply, and `LabelAlphaModel` injectively
maps those nominal occurrences into stable manifest identities. Literal stable
labels and local labels share one `AuthoredLabel` normalization surface.
-/

namespace Grass.Construct.Source

open Grass.Core Grass.CFG

/-- Phantom identity domain for macro-local label occurrences. -/
inductive LabelTag : Type

/-- Nominal identity of one macro-local label occurrence. -/
abbrev LabelId := Uid LabelTag

/-- Monotone identity supply for macro-local labels. -/
abbrev LabelSupply := FreshSupply LabelTag

/-- One hygienic local label with a non-authoritative diagnostic hint. -/
structure LabelToken where
  id : LabelId
  hint : String
deriving Repr, DecidableEq

/-- Result of minting one label token from an exact input supply. -/
structure MintedLabel (before : LabelSupply) where
  token : LabelToken
  after : LabelSupply
  idExact : token.id = before.fresh.1
  afterExact : after = before.fresh.2

namespace LabelSupply

/-- Mint one hygienic label and advance the supply exactly once. -/
def mint (before : LabelSupply) (hint : String) : MintedLabel before :=
  ⟨⟨before.fresh.1, hint⟩, before.fresh.2, rfl, rfl⟩

end LabelSupply

namespace MintedLabel

variable {before : LabelSupply}

/-- The newly minted label identity was not issued by the input supply. -/
theorem freshBefore (minted : MintedLabel before) :
    ¬before.Issued minted.token.id := by
  rw [minted.idExact]
  exact FreshSupply.fresh_not_issued before

/-- The advanced supply records the newly minted label identity. -/
theorem issuedAfter (minted : MintedLabel before) :
    minted.after.Issued minted.token.id := by
  rw [minted.afterExact, minted.idExact]
  exact FreshSupply.issued_fresh before before.fresh.1 |>.mpr (.inr rfl)

/-- No later mint in the same history can reuse this local label identity. -/
theorem neverReissued (minted : MintedLabel before) {later : LabelSupply}
    (reachable : FreshSupply.Reachable minted.after later) :
    later.fresh.1 ≠ minted.token.id :=
  FreshSupply.never_reissued reachable minted.issuedAfter

end MintedLabel

/-- Injective alpha-normalization of local identities into stable block IDs. -/
structure LabelAlphaModel where
  toBlock : LabelId → BlockId
  injective : Function.Injective toBlock

/-- Authored target form before alpha-normalization closes local identities. -/
inductive AuthoredLabel where
  | stable (block : BlockId)
  | local (token : LabelToken)
deriving Repr, DecidableEq

namespace AuthoredLabel

/-- Resolve a literal stable label or hygienic local label to its manifest ID. -/
def alphaNormalize (model : LabelAlphaModel) : AuthoredLabel → BlockId
  | .stable block => block
  | .local token => model.toBlock token.id

@[simp] theorem alphaNormalize_stable (model : LabelAlphaModel) (block : BlockId) :
    (AuthoredLabel.stable block).alphaNormalize model = block := rfl

@[simp] theorem alphaNormalize_local (model : LabelAlphaModel)
    (token : LabelToken) :
    (AuthoredLabel.local token).alphaNormalize model = model.toBlock token.id := rfl

/-- Distinct nominal local identities normalize to distinct stable block IDs. -/
theorem alphaNormalize_local_ne (model : LabelAlphaModel)
    (left right : LabelToken) (distinct : left.id ≠ right.id) :
    (AuthoredLabel.local left).alphaNormalize model ≠
      (AuthoredLabel.local right).alphaNormalize model := by
  intro equal
  exact distinct (model.injective equal)

end AuthoredLabel

/-- Two sequentially minted labels are hygienically distinct. -/
theorem sequentialLabelIdsDistinct {before : LabelSupply} (first : MintedLabel before)
    (second : MintedLabel first.after) : second.token.id ≠ first.token.id := by
  rw [second.idExact]
  exact first.neverReissued (.refl first.after)

/-- Sequential local labels alpha-normalize to distinct stable block IDs. -/
theorem sequentialAlphaLabelsDistinct {before : LabelSupply}
    (model : LabelAlphaModel) (first : MintedLabel before)
    (second : MintedLabel first.after) :
    (AuthoredLabel.local second.token).alphaNormalize model ≠
      (AuthoredLabel.local first.token).alphaNormalize model :=
  AuthoredLabel.alphaNormalize_local_ne model second.token first.token
    (sequentialLabelIdsDistinct first second)

end Grass.Construct.Source
