import Grass.Process.Spec

/-!
# Protocol registries

`docs/PROCESS.md` §3 stores protocols in a registry and has child requests carry
keys rather than embed a `ProcessSpec`:

> Protocol values are stored in a universe-stratified registry; child requests
> carry keys, never recursively embed an arbitrary `ProcessSpec`.

`docs/PROCESS_SHARDING.md` §2 says what the registry must *not* be:

> A large program does not declare `inductive WholeProgramProcessKind`. Registry
> merge preserves the nominal identity of every unaffected entry.

and lists "a closed whole-program `ProcessKind`, `ProtocolKey`, or role sum" and
"one registry value imported by every process module" among its foundational
failures.

## How the sum is avoided

A `RegistryFragment` is what one module owns: a scope identity and its own local
key type. Nothing imports anyone else's fragment. `merge` builds a registry
whose key type is the `Sum` of two key types, at the aggregate that composes
them, and `RegistryEmbedding` witnesses that every prior key keeps its protocol
and its scope.

The binary `Sum` at a merge is not the thing the sharding document forbids. What
it forbids is a single inductive declared once and imported everywhere, so that
adding a role changes a type every module depends on. Here, adding a role to one
fragment changes that fragment and the merges above it — the bounded-fanout
aggregate path of `docs/OLEAN_SHARDING.md` §3 — and no sibling.

## Universes

`Key`, the protocols' interface types, and the protocols' private types live in
three independent universes. This is not generality
for its own sake: `docs/PROCESS.md` §4 makes a flattened realization's private
state the whole logical network of the plan it came from, so `flatten` produces
a `ProcessSpec` strictly above the protocols it was built from, and
`RegisteredProcess` then asks for an embedding across that shift. A registry
frozen at one universe would have to be rewritten when flattening arrives;
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.2 records the decision.
-/

namespace Grass.Process

universe u w v

/--
A reviewed nominal scope: the identity of the module that owns a family of keys.

Path segments rather than one string, because scopes nest and a merge has to
compare them structurally. `docs/PROCESS_SHARDING.md` §1 requires a *reviewed
nominal identity*; a content hash is a cache key and is not this.
-/
structure ScopeId where
  /-- The scope path, outermost first. -/
  path : List String
  deriving DecidableEq, Repr

-- The universe linter objects that `u` and `v` appear only inside a `max`. That
-- is exactly the intent: a registry's keys and its protocols are independently
-- universe-polymorphic, so that `flatten` can register a process built from the
-- registry back into an extension of it. See the module note.
set_option linter.checkUnivs false in
/--
What one module owns: a scope and its own local key type.

No module imports another's fragment. This is the unit
`docs/PROCESS_SHARDING.md` §2 calls a `ProcessRegistryFragment`.
-/
structure RegistryFragment : Type (max (u + 1) (w + 1) (v + 1)) where
  /-- The nominal scope this fragment owns. -/
  scope : ScopeId
  /-- The fragment's own key type. -/
  Local : Type v
  /-- The protocol each local key names. -/
  protocol : Local → ProcessSpec.{u, w}

set_option linter.checkUnivs false in
/--
A registry: keys, their protocols, and the scope that owns each key.

`scope` is a field rather than a derived fact because merge has to preserve it:
`docs/PROCESS_SHARDING.md` §2 requires that "registry merge preserves the
nominal identity of every unaffected entry", and an identity that were
recomputed from position would not be preserved.
-/
structure ProtocolRegistry : Type (max (u + 1) (w + 1) (v + 1)) where
  /-- The key type. -/
  Key : Type v
  /-- The protocol each key names. -/
  protocol : Key → ProcessSpec.{u, w}
  /-- Which fragment owns each key. -/
  scope : Key → ScopeId

namespace RegistryFragment

/-- The single-fragment registry. -/
def toRegistry (fragment : RegistryFragment.{u, w, v}) : ProtocolRegistry.{u, w, v} where
  Key := fragment.Local
  protocol := fragment.protocol
  scope := fun _ => fragment.scope

@[simp] theorem toRegistry_protocol (fragment : RegistryFragment.{u, w, v})
    (key : fragment.Local) :
    fragment.toRegistry.protocol key = fragment.protocol key := rfl

@[simp] theorem toRegistry_scope (fragment : RegistryFragment.{u, w, v})
    (key : fragment.Local) :
    fragment.toRegistry.scope key = fragment.scope := rfl

end RegistryFragment

/--
An embedding of one registry into another: every key keeps its protocol and its
scope.

`docs/PROCESS.md` §4 requires exactly this of `RegisteredProcess.includeExisting`
— "an embedding of every existing key" — and the reason the protocol equation is
here rather than a promise is that a registry extension which quietly changed
what an existing key meant would invalidate every proof indexed by that key
while type-checking.
-/
structure RegistryEmbedding (small large : ProtocolRegistry.{u, w, v}) where
  /-- Where each old key lands. -/
  embed : small.Key → large.Key
  /-- Distinct old keys stay distinct. -/
  injective : ∀ left right, embed left = embed right → left = right
  /-- Each old key names the same protocol. -/
  protocolExact : ∀ key, large.protocol (embed key) = small.protocol key
  /-- Each old key keeps its owning scope. -/
  scopeExact : ∀ key, large.scope (embed key) = small.scope key

namespace RegistryEmbedding

variable {small middle large : ProtocolRegistry.{u, w, v}}

/-- The identity embedding. -/
def refl (registry : ProtocolRegistry.{u, w, v}) : RegistryEmbedding registry registry where
  embed := id
  injective := fun _ _ equal => equal
  protocolExact := fun _ => rfl
  scopeExact := fun _ => rfl

/-- Embeddings compose, so a chain of registry extensions is one embedding. -/
def trans (first : RegistryEmbedding small middle)
    (second : RegistryEmbedding middle large) : RegistryEmbedding small large where
  embed := second.embed ∘ first.embed
  injective := fun left right equal =>
    first.injective left right (second.injective _ _ equal)
  protocolExact := fun key => by
    simp only [Function.comp_apply, second.protocolExact, first.protocolExact]
  scopeExact := fun key => by
    simp only [Function.comp_apply, second.scopeExact, first.scopeExact]

end RegistryEmbedding

namespace ProtocolRegistry

/--
Two registries whose scopes do not overlap.

The disjointness `docs/PROCESS_SHARDING.md` §2 requires of `merge`. It is stated
over scopes rather than over keys because scopes are the reviewed nominal
identities; two fragments may perfectly well use the same local key type.
-/
def ScopesDisjoint (left right : ProtocolRegistry.{u, w, v}) : Prop :=
  ∀ (leftKey : left.Key) (rightKey : right.Key),
    left.scope leftKey ≠ right.scope rightKey

/--
Merge two registries with disjoint scopes.

The key type is a `Sum` formed *here*, at the aggregate, not declared once and
imported. See the module note.
-/
def merge (left right : ProtocolRegistry.{u, w, v})
    (_disjoint : ScopesDisjoint left right) : ProtocolRegistry.{u, w, v} where
  Key := Sum left.Key right.Key
  protocol := fun key => key.elim left.protocol right.protocol
  scope := fun key => key.elim left.scope right.scope

/-- The left registry embeds into the merge. -/
def mergeLeft (left right : ProtocolRegistry.{u, w, v})
    (disjoint : ScopesDisjoint left right) :
    RegistryEmbedding left (merge left right disjoint) where
  embed := Sum.inl
  injective := fun _ _ equal => Sum.inl.inj equal
  protocolExact := fun _ => rfl
  scopeExact := fun _ => rfl

/-- The right registry embeds into the merge. -/
def mergeRight (left right : ProtocolRegistry.{u, w, v})
    (disjoint : ScopesDisjoint left right) :
    RegistryEmbedding right (merge left right disjoint) where
  embed := Sum.inr
  injective := fun _ _ equal => Sum.inr.inj equal
  protocolExact := fun _ => rfl
  scopeExact := fun _ => rfl

/--
The two embeddings have disjoint images.

Together with `mergeLeft` and `mergeRight` this is the whole content of "merge
preserves the nominal identity of every unaffected entry": every old key is
still there, still means the same protocol, and no two old keys from different
fragments have collided.
-/
theorem merge_images_disjoint (left right : ProtocolRegistry.{u, w, v})
    (disjoint : ScopesDisjoint left right)
    (leftKey : left.Key) (rightKey : right.Key) :
    (mergeLeft left right disjoint).embed leftKey ≠
      (mergeRight left right disjoint).embed rightKey := by
  intro equal
  have sides : (Sum.inl leftKey : Sum left.Key right.Key).isLeft =
      (Sum.inr rightKey : Sum left.Key right.Key).isLeft :=
    congrArg Sum.isLeft equal
  simp at sides

/--
A key's scope is preserved by merge on both sides.

Stated separately because a scope check is what a provider-coherence fold at an
aggregate actually performs, and it should not have to unfold `Sum.elim`.
-/
@[simp] theorem merge_scope_inl (left right : ProtocolRegistry.{u, w, v})
    (disjoint : ScopesDisjoint left right) (key : left.Key) :
    (merge left right disjoint).scope (Sum.inl key) = left.scope key := rfl

@[simp] theorem merge_scope_inr (left right : ProtocolRegistry.{u, w, v})
    (disjoint : ScopesDisjoint left right) (key : right.Key) :
    (merge left right disjoint).scope (Sum.inr key) = right.scope key := rfl

end ProtocolRegistry

/--
A request to a registered protocol: a key and the protocol's own request value.

`docs/PROCESS.md` §3: "child requests carry keys, never recursively embed an
arbitrary `ProcessSpec`". That is the whole reason this type exists — a field of
type `ProcessSpec` here would make the child relation non-well-founded in the
universe hierarchy and would put a whole protocol inside every parent's state.
-/
structure ChildRequest (registry : ProtocolRegistry.{u, w, v}) : Type (max w v) where
  /-- Which protocol. -/
  key : registry.Key
  /-- Its request. -/
  request : (registry.protocol key).Request

end Grass.Process
