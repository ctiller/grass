import Grass.Std.Logical.Bag

/-!
# `Bag`, re-exported from its owner

`docs/MODULES.md` gives pure collections and their algebraic laws to
`Grass.Std.Logical`, and this module's own custody note recorded itself as
temporary. `Grass/Std/Logical/Bag.lean` is the permanent home and holds the
implementation; what remains here is the name, aliased.

## Why an `export` rather than editing the consumers

`Bag` is named by fourteen modules under `Grass/Process/` and sixteen fixtures
under `Tests/Process/`, most of which never import this module directly -- they
receive the name through `Grass.Process.Spec`. Lean's `open` is not inherited by
importers, so pointing each of them at the new owner means an edit in every one.
`export` *is* inherited, so one alias here reaches all thirty.

The list below is every constant in the owning namespace, generated from
`Tools/DeclNames.lean` rather than written by hand, because a hand-written list
is one that silently omits whatever was added last.

## What this does and does not settle

`Grass.Process.Bag.card` and `Grass.Std.Logical.Bag.card` are now the same
constant, so a proof about one is a proof about the other. That is the property
the duplicate did not have: before this, the two namespaces held 57 distinct
constants with identical statements and no way for a proof to cross between
them.

It does not remove the name `Grass.Process.Bag`. If that name should go too,
every site naming it has to change, and that is the thirty-file edit this
commit is deliberately not making.
-/

namespace Grass.Process

export Grass.Std.Logical (Bag)

namespace Bag
export Grass.Std.Logical.Bag (
  ConsumeExactlyOneMatching Mem add_assoc add_comm add_cons add_zero append
  card card_add card_cons card_map card_ofList card_zero cons
  cons_eq_singleton_add cons_injective_right consume_iff_mem empty instAdd
  instEmptyCollection instMembership instSingleton instZero map map_add
  map_cons map_consume map_ofList map_zero mem_add mem_cons mem_map
  mem_ofList mem_singleton mem_zero not_consume_zero ofList ofList_append
  ofList_cons ofList_nil singleton singleton_eq zero_add)
end Bag

namespace Bag.ConsumeExactlyOneMatching
export Grass.Std.Logical.Bag.ConsumeExactlyOneMatching (
  card mem remainder_unique)
end Bag.ConsumeExactlyOneMatching

end Grass.Process
