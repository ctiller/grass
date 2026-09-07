import Grass.Construct.Layout.Core

/-!
# Lexical stack layouts

The ordinary stack layout constructor gives every named object one fixed,
nonoverlapping range and one declared lexical scope.  Parent scopes must precede
children, so the finite scope list is acyclic by construction order.  Reuse and
overlays require separate constructors rather than weakening this checker.
-/

namespace Grass.Construct.Layout

open Grass.Core Grass.Memory

universe u

/-- Stable identity of one lexical stack scope. -/
structure ScopeId where
  id : Name
deriving Repr, DecidableEq

/-- One lexical scope and its optional already-declared parent. -/
structure ScopeDecl where
  id : ScopeId
  parent : Option ScopeId
deriving Repr, DecidableEq

/-- One named stack object at an explicit frame-relative byte offset. -/
structure StackObject (profile : LayoutProfile) where
  name : Name
  repr : ObjectRepr profile
  offset : Nat
  scope : ScopeId
deriving Repr, DecidableEq

namespace StackObject

variable {profile : LayoutProfile}

/-- Exact half-open frame-relative byte range occupied by the object. -/
def byteRange (object : StackObject profile) : ByteRange :=
  ⟨object.offset, object.repr.size⟩

end StackObject

/-- Selected ordinary fixed-size lexical stack frame. -/
structure StackLayout (profile : LayoutProfile) where
  scopes : List ScopeDecl
  objects : List (StackObject profile)
  size : Nat
  alignment : Nat
  maxSize : Nat
deriving Repr, DecidableEq

namespace StackLayout

variable {profile : LayoutProfile}

/-- Lexical scope identities in declaration order. -/
def scopeIds (layout : StackLayout profile) : List ScopeId :=
  layout.scopes.map ScopeDecl.id

/-- Stack object names in layout order. -/
def objectNames (layout : StackLayout profile) : List Name :=
  layout.objects.map StackObject.name

private def scopesOrderedFrom : List ScopeId → List ScopeDecl → Bool
  | _, [] => true
  | declared, scope :: rest =>
      (match scope.parent with
       | none => true
       | some parent => declared.contains parent) &&
      scopesOrderedFrom (declared ++ [scope.id]) rest

/-- Whether each lexical parent precedes its child declaration. -/
def scopesOrdered (layout : StackLayout profile) : Bool :=
  scopesOrderedFrom [] layout.scopes

/-- Local representation, alignment, containment, and scope check. -/
def objectWellFormed (layout : StackLayout profile)
    (object : StackObject profile) : Bool :=
  decide (0 < object.repr.size) &&
  object.repr.wellFormed &&
  decide (IsAligned object.offset object.repr.alignment) &&
  decide (object.byteRange.WithinBound layout.size) &&
  decide (layout.alignment % object.repr.alignment = 0) &&
  layout.scopeIds.contains object.scope

/-- Pairwise spatial separation for the ordinary fixed frame constructor. -/
def objectsDisjoint (layout : StackLayout profile) : Bool :=
  decide (layout.objects.Pairwise fun left right =>
    left.byteRange.Disjoint right.byteRange)

/-- Executable ordinary stack-layout checker. -/
def wellFormed (layout : StackLayout profile) : Bool :=
  decide layout.scopeIds.Nodup &&
  layout.scopesOrdered &&
  decide layout.objectNames.Nodup &&
  decide (0 < layout.alignment) &&
  profile.acceptsAlignment layout.alignment &&
  decide (IsAligned layout.size layout.alignment) &&
  decide (layout.size ≤ layout.maxSize) &&
  layout.objects.all (layout.objectWellFormed) &&
  layout.objectsDisjoint

/-- Certificate-facing statement for `StackLayout.wellFormed`. -/
def WellFormed (layout : StackLayout profile) : Prop := layout.wellFormed = true

instance (layout : StackLayout profile) : Decidable layout.WellFormed :=
  inferInstanceAs (Decidable (layout.wellFormed = true))

/-- Public decomposition of ordinary stack-layout closure. -/
@[simp] theorem wellFormed_iff (layout : StackLayout profile) :
    layout.WellFormed ↔
      (((((((layout.scopeIds.Nodup ∧ layout.scopesOrdered = true) ∧
        layout.objectNames.Nodup) ∧ 0 < layout.alignment) ∧
        profile.acceptsAlignment layout.alignment = true) ∧
        IsAligned layout.size layout.alignment) ∧
        layout.size ≤ layout.maxSize) ∧
        layout.objects.all layout.objectWellFormed = true) ∧
        layout.objectsDisjoint = true := by
  simp [WellFormed, wellFormed]

end StackLayout

/-- Resources that must be absent when one lexical stack scope exits. -/
structure ScopeExit (Resource : Type u) where
  escapingAddresses : List Name
  liveLoans : List Resource
  liveObligations : List Resource
deriving Repr

namespace ScopeExit

/-- Executable lexical-exit checker. -/
def wellFormed {Resource : Type u} (exit : ScopeExit Resource) : Bool :=
  exit.escapingAddresses.isEmpty &&
  exit.liveLoans.isEmpty &&
  exit.liveObligations.isEmpty

/-- Certificate-facing statement for `ScopeExit.wellFormed`. -/
def WellFormed {Resource : Type u} (exit : ScopeExit Resource) : Prop :=
  exit.wellFormed = true

instance {Resource : Type u} (exit : ScopeExit Resource) : Decidable exit.WellFormed :=
  inferInstanceAs (Decidable (exit.wellFormed = true))

/-- Public decomposition of lexical scope-exit closure. -/
@[simp] theorem wellFormed_iff {Resource : Type u} (exit : ScopeExit Resource) :
    exit.WellFormed ↔
      (exit.escapingAddresses = [] ∧ exit.liveLoans = []) ∧
        exit.liveObligations = [] := by
  simp [WellFormed, wellFormed]

end ScopeExit

end Grass.Construct.Layout
