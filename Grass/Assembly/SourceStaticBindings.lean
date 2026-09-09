import Grass.Assembly.StaticSection
import Grass.Assembly.SourceResolve

namespace Grass.Assembly.SourceStaticBindings
open Grass.Artifact.PE

structure Binding (plan : ImagePlan) {table : StaticObjects.Table}
    (layout : StaticSection.Layout table) (sectionIndex : Nat) where
  name : String
  object : StaticSection.Object
  span : StaticSection.ObjectSpan plan layout sectionIndex name object

def Binding.sourceSymbol {plan : ImagePlan} {table : StaticObjects.Table}
    {layout : StaticSection.Layout table} {sectionIndex : Nat}
    (binding : Binding plan layout sectionIndex) : SourceResolve.StaticSymbol :=
  ⟨binding.name, binding.span.rva, binding.object.declaration.bytes.length⟩

def resolveOne? (plan : ImagePlan) {table : StaticObjects.Table}
    (layout : StaticSection.Layout table) (sectionIndex : Nat) (name : String) :
    Option (Binding plan layout sectionIndex) := do
  let found ← StaticSection.resolveSpan? plan layout sectionIndex name
  pure ⟨name, found.1, found.2⟩

structure Result (plan : ImagePlan) {table : StaticObjects.Table}
    (layout : StaticSection.Layout table) (sectionIndex : Nat) where
  bindings : List (Binding plan layout sectionIndex)
  namesExact : bindings.map Binding.name = table.declarations.map StaticObjects.Declaration.name

def resolve? (plan : ImagePlan) {table : StaticObjects.Table}
    (layout : StaticSection.Layout table) (sectionIndex : Nat) :
    Option (Result plan layout sectionIndex) := do
  let bindings ← (table.declarations.map StaticObjects.Declaration.name).mapM
    (resolveOne? plan layout sectionIndex)
  if exact : bindings.map Binding.name = table.declarations.map StaticObjects.Declaration.name then
    some ⟨bindings, exact⟩
  else none

def Result.sourceSymbols {plan : ImagePlan} {table : StaticObjects.Table}
    {layout : StaticSection.Layout table} {sectionIndex : Nat}
    (result : Result plan layout sectionIndex) : List SourceResolve.StaticSymbol :=
  result.bindings.map Binding.sourceSymbol

theorem Result.sourceNames {plan : ImagePlan} {table : StaticObjects.Table}
    {layout : StaticSection.Layout table} {sectionIndex : Nat}
    (result : Result plan layout sectionIndex) :
    result.sourceSymbols.map SourceResolve.StaticSymbol.name =
      table.declarations.map StaticObjects.Declaration.name := by
  simpa [Result.sourceSymbols, Binding.sourceSymbol, List.map_map, Function.comp_def]
    using result.namesExact

theorem Result.uniqueNames {plan : ImagePlan} {table : StaticObjects.Table}
    {layout : StaticSection.Layout table} {sectionIndex : Nat}
    (result : Result plan layout sectionIndex) :
    (result.sourceSymbols.map SourceResolve.StaticSymbol.name).Nodup := by
  rw [result.sourceNames]
  exact table.names_unique

theorem Binding.payload_exact {plan : ImagePlan} {table : StaticObjects.Table}
    {layout : StaticSection.Layout table} {sectionIndex : Nat}
    (binding : Binding plan layout sectionIndex) :
    (binding.span.placedSection.source.contents.drop binding.object.offset).take
        binding.sourceSymbol.byteLength = binding.object.declaration.bytes := by
  rw [binding.span.sourceExact]
  exact of_decide_eq_true (List.all_eq_true.mp layout.payloadsExact _ binding.span.objectMember)

theorem Binding.address_exact {plan : ImagePlan} {table : StaticObjects.Table}
    {layout : StaticSection.Layout table} {sectionIndex : Nat}
    (binding : Binding plan layout sectionIndex) :
    binding.sourceSymbol.address = binding.span.placedSection.virtualSpan.start +
      binding.object.offset := binding.span.rva_eq

end Grass.Assembly.SourceStaticBindings
