/-!
# Stable foundation identifiers

Names used in certificate summaries are data, not proof authority.  The pair
keeps an owner's namespace separate from its local name without imposing a
closed registry on downstream libraries.
-/

namespace Grass

/-- A stable, open-world identifier owned by `namespace`. -/
structure StableId where
  owner : String
  localName : String
deriving Repr, DecidableEq, BEq, Hashable

namespace StableId

/-- Render an identifier for human diagnostics.

This dotted form is not an injective serialization; manifests must retain the
two structure fields or use a separately specified encoding. -/
def render (id : StableId) : String :=
  if id.owner.isEmpty then id.localName
  else id.owner ++ "." ++ id.localName

@[simp] theorem render_of_empty_namespace (localName : String) :
    (StableId.mk "" localName).render = localName := by
  simp [render]

end StableId

/-- Stable identity of one independently discharged theorem demand. -/
structure RequirementKey where
  id : StableId
deriving Repr, DecidableEq, BEq, Hashable

end Grass
