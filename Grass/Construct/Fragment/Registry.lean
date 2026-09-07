import Grass.Construct.Fragment.Generator

/-!
# Explicit verified-fragment constructor closure

Authored source receives a finite `ConstructorClosure` as a dependent input.
Lookup is therefore limited to that value: this module performs no namespace
scan and defines no ambient or global registry. Heterogeneous constructor
parameter types remain tied to the exact selected constructor.
-/

namespace Grass.Construct.Fragment

open Grass.CFG

universe u v w

/-- One named verified-fragment constructor with its exact parameter type. -/
structure Constructor (Instruction : Type u) (State : Type v) (Effect : Type w)
    (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  id : FragmentId
  Parameter : Type
  generator : Generator Parameter Instruction State Effect semantics effectModel

/-- The finite constructor set explicitly supplied to one authored source. -/
structure ConstructorClosure (Instruction : Type u) (State : Type v)
    (Effect : Type w) (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  constructors : List (Constructor Instruction State Effect semantics effectModel)

namespace ConstructorClosure

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}

/-- Constructor identities in exact supplied order. -/
def ids (closure : ConstructorClosure Instruction State Effect semantics effectModel) :
    List FragmentId :=
  closure.constructors.map Constructor.id

/-- Resolve a constructor only inside the explicitly supplied closure. -/
def lookup? (closure : ConstructorClosure Instruction State Effect semantics effectModel)
    (id : FragmentId) :
    Option (Constructor Instruction State Effect semantics effectModel) :=
  closure.constructors.find? fun constructor => constructor.id == id

/-- A successful lookup returns the exact requested constructor identity. -/
theorem id_of_lookup? {closure : ConstructorClosure Instruction State Effect
    semantics effectModel} {id : FragmentId}
    {constructor : Constructor Instruction State Effect semantics effectModel}
    (h : closure.lookup? id = some constructor) : constructor.id = id := by
  have hmatch : (constructor.id == id) = true := by
    exact List.find?_some
      (p := fun candidate : Constructor Instruction State Effect semantics effectModel =>
        candidate.id == id)
      (by simpa [lookup?] using h)
  exact LawfulBEq.eq_of_beq hmatch

/-- A successful lookup returns an entry from the supplied finite closure. -/
theorem mem_of_lookup? {closure : ConstructorClosure Instruction State Effect
    semantics effectModel} {id : FragmentId}
    {constructor : Constructor Instruction State Effect semantics effectModel}
    (h : closure.lookup? id = some constructor) :
    constructor ∈ closure.constructors :=
  List.mem_of_find?_eq_some h

/-- Closure validity rejects ambiguous constructor identities. -/
def WellFormed
    (closure : ConstructorClosure Instruction State Effect semantics effectModel) :
    Prop := closure.ids.Nodup

instance (closure : ConstructorClosure Instruction State Effect semantics effectModel) :
    Decidable closure.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Executable constructor-closure validity check. -/
def wellFormed
    (closure : ConstructorClosure Instruction State Effect semantics effectModel) :
    Bool := decide closure.WellFormed

@[simp] theorem wellFormed_iff
    (closure : ConstructorClosure Instruction State Effect semantics effectModel) :
    closure.wellFormed ↔ closure.WellFormed := by
  simp [wellFormed]

end ConstructorClosure

/-- Checked constructor input whose nominal resolution is unambiguous. -/
structure CheckedConstructorClosure
    {Instruction : Type u} {State : Type v} {Effect : Type w}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (closure : ConstructorClosure Instruction State Effect semantics effectModel) :
    Type (max u v w) where
  valid : closure.WellFormed

/-- Constructor-closure validation failure with the exact conflicting ledger. -/
structure ConstructorClosureError where
  ids : List FragmentId
deriving Repr, DecidableEq

/-- Reject an ambiguous supplied constructor closure before source elaboration. -/
def checkConstructorClosure
    {Instruction : Type u} {State : Type v} {Effect : Type w}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (closure : ConstructorClosure Instruction State Effect semantics effectModel) :
    Except ConstructorClosureError (CheckedConstructorClosure closure) :=
  if valid : closure.WellFormed then .ok ⟨valid⟩
  else .error ⟨closure.ids⟩

/-- A constructor resolved from one exact supplied closure. -/
structure SelectedConstructor
    {Instruction : Type u} {State : Type v} {Effect : Type w}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    (closure : ConstructorClosure Instruction State Effect semantics effectModel)
    (_checked : CheckedConstructorClosure closure)
    (requested : FragmentId) where
  constructor : Constructor Instruction State Effect semantics effectModel
  resolved : closure.lookup? requested = some constructor

namespace SelectedConstructor

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {closure : ConstructorClosure Instruction State Effect semantics effectModel}
  {checked : CheckedConstructorClosure closure}
  {requested : FragmentId}

/-- The selected constructor has exactly the requested identity. -/
theorem id_exact (selected : SelectedConstructor closure checked requested) :
    selected.constructor.id = requested :=
  ConstructorClosure.id_of_lookup? selected.resolved

/-- The selected constructor belongs to the exact supplied closure. -/
theorem member (selected : SelectedConstructor closure checked requested) :
    selected.constructor ∈ closure.constructors :=
  ConstructorClosure.mem_of_lookup? selected.resolved

end SelectedConstructor

namespace CheckedConstructorClosure

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {closure : ConstructorClosure Instruction State Effect semantics effectModel}

/-- Resolve a requested constructor from this checked explicit input. -/
def select? (_checked : CheckedConstructorClosure closure) (requested : FragmentId) :
    Option (SelectedConstructor closure _checked requested) :=
  match h : closure.lookup? requested with
  | none => none
  | some constructor => some ⟨constructor, h⟩

end CheckedConstructorClosure

/-- Failed constructor selection with the exact requested and available identities. -/
structure ConstructorSelectionError where
  requested : FragmentId
  available : List FragmentId
deriving Repr, DecidableEq

namespace CheckedConstructorClosure

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {closure : ConstructorClosure Instruction State Effect semantics effectModel}

/-- Resolve a constructor or retain an exact source-closure diagnostic. -/
def select (checked : CheckedConstructorClosure closure) (requested : FragmentId) :
    Except ConstructorSelectionError (SelectedConstructor closure checked requested) :=
  match h : closure.lookup? requested with
  | none => .error ⟨requested, closure.ids⟩
  | some constructor => .ok ⟨constructor, h⟩

end CheckedConstructorClosure

/-- A typed application whose parameter type comes from its selected constructor. -/
structure ConstructorApplication
    {Instruction : Type u} {State : Type v} {Effect : Type w}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    {closure : ConstructorClosure Instruction State Effect semantics effectModel}
    {checked : CheckedConstructorClosure closure} {requested : FragmentId}
    (selected : SelectedConstructor closure checked requested) where
  parameter : selected.constructor.Parameter

namespace ConstructorApplication

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {closure : ConstructorClosure Instruction State Effect semantics effectModel}
  {checked : CheckedConstructorClosure closure} {requested : FragmentId}
  {selected : SelectedConstructor closure checked requested}

/-- The exact verified fragment selected by this typed application. -/
def fragment (application : ConstructorApplication selected) :
    VerifiedFragment semantics effectModel
      (selected.constructor.generator.contract application.parameter) :=
  selected.constructor.generator.generate application.parameter

/-- Hierarchical source marking the exact selected constructor application. -/
def source (application : ConstructorApplication selected) : Source Instruction :=
  .generated requested application.fragment.source

/-- Lift the selected verified fragment while retaining its constructor origin. -/
def verified (application : ConstructorApplication selected) :
    VerifiedFragment semantics effectModel
      (selected.constructor.generator.contract application.parameter) where
  source := application.source
  contractWellFormed := application.fragment.contractWellFormed
  effects := application.fragment.effects
  effectsExact := by
    simpa [source] using application.fragment.effectsExact
  localCorrect := by
    simpa [source] using application.fragment.localCorrect

/-- Constructor-origin wrapping leaves exact instruction expansion unchanged. -/
@[simp] theorem source_expand (application : ConstructorApplication selected) :
    application.source.expand = application.fragment.source.expand := by
  simp [source]

/-- The lifted certificate expands to exactly the selected generated fragment. -/
@[simp] theorem verified_source_expand
    (application : ConstructorApplication selected) :
    application.verified.source.expand = application.fragment.source.expand := by
  simp [verified]

end ConstructorApplication

end Grass.Construct.Fragment
