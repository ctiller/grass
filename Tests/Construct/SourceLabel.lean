import Grass.Construct.Source.Label

/-!
# Hygienic authored-label fixtures

Fixtures pin fresh sequential minting, literal preservation, local
alpha-normalization, and stable-ID distinction for two equal-hint labels.
-/

namespace Grass.Tests.Construct.SourceLabel

open Grass Grass.Core Grass.CFG Grass.Construct.Source

private def supply : LabelSupply := FreshSupply.initial
private def first : MintedLabel supply := supply.mint "loop"
private def second : MintedLabel first.after := first.after.mint "loop"

private def stable : BlockId := ⟨⟨"test.label", "literal"⟩⟩

example : ¬supply.Issued first.token.id := first.freshBefore
example : first.after.Issued first.token.id := first.issuedAfter
example : second.token.id ≠ first.token.id := sequentialLabelIdsDistinct first second
example (model : LabelAlphaModel) :
    (AuthoredLabel.stable stable).alphaNormalize model = stable := rfl
example (model : LabelAlphaModel) :
    (AuthoredLabel.local first.token).alphaNormalize model =
      model.toBlock first.token.id := rfl
example (model : LabelAlphaModel) :
    (AuthoredLabel.local second.token).alphaNormalize model ≠
      (AuthoredLabel.local first.token).alphaNormalize model :=
  sequentialAlphaLabelsDistinct model first second

end Grass.Tests.Construct.SourceLabel
