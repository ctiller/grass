import Grass.Platform.Win32.WriteFileCall
import Grass.Platform.Win32.Signatures
import Grass.Std.Logical.Text

/-!
# Logical dispatch through a materialized PE import

This module deterministically relates an observed indirect `CALL` address and
loaded target value to the checked image's own import layout and target table.
It establishes a logical import binding only.  In particular, the retained DLL
name is data from the image; no Windows DLL identity, export-table identity, or
native provider adequacy follows from a successful selection.
-/

namespace Grass.Platform.Win32.ApiDispatch

open Grass.Std.Logical Grass.Artifact
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Loader

/-- The API variant named by a heterogeneous protocol request. -/
def requestApi : ApiRequest → Signatures.Api
  | .getStdHandle _ => .getStdHandle
  | .writeFile _ => .writeFile
  | .exitProcess _ => .exitProcess

/-- Resolve only the three fixed native symbol byte strings. -/
def apiForBytes? (name : Grass.Std.Logical.ByteArray) : Option Signatures.Api :=
  Signatures.apis.find? fun api => Text.utf8 (Signatures.apiName api) == name

theorem apiForBytes?_exact {name : Grass.Std.Logical.ByteArray} {api : Signatures.Api}
    (found : apiForBytes? name = some api) :
    Text.utf8 (Signatures.apiName api) = name := by
  have selected := List.find?_some found
  simpa using selected

/-- Evidence returned by the computed selector.  Every identity and coordinate
is recovered from the actual plan and target inputs at the retained indices. -/
structure Binding {image : ImageInput} {inputs : EntryInputs}
    (_loaded : LoadedImage image inputs)
    (observedEA observedTarget : BitVec 64) where
  api : Signatures.Api
  libraryIndex : Nat
  library : PE.ImportLibraryLayout
  libraryLookup : image.plan.layout.importLayouts.get? libraryIndex = some library
  libraryName : Grass.Std.Logical.ByteArray
  libraryNameExact : libraryName = library.library.name
  symbolIndex : Nat
  symbol : PE.ImportSymbol
  symbolLookup : library.library.symbols.get? symbolIndex = some symbol
  symbolNameExact : symbol.name = Text.utf8 (Signatures.apiName api)
  rva : Nat
  rvaLookup : image.plan.layout.importAddressRva? libraryIndex symbolIndex = some rva
  targetLibrary : Vec (BitVec 64)
  targetLibraryLookup : inputs.targets.get? libraryIndex = some targetLibrary
  target : BitVec 64
  targetLookup : targetLibrary.get? symbolIndex = some target
  addressFits : (preferredBase image).toNat + rva < 2 ^ 64
  addressExact : observedEA.toNat = (preferredBase image).toNat + rva
  targetExact : observedTarget = target

/-- Try one actual library/symbol occurrence.  The checks include full natural
address equality and nonwrapping, rather than truncated `BitVec` equality. -/
def candidateAt? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs)
    (observedEA observedTarget : BitVec 64) (libraryIndex symbolIndex : Nat) :
    Option (Binding loaded observedEA observedTarget) :=
  match hlibrary : image.plan.layout.importLayouts.get? libraryIndex with
  | none => none
  | some library =>
    match hsymbol : library.library.symbols.get? symbolIndex with
    | none => none
    | some symbol =>
      match hapi : apiForBytes? symbol.name with
      | none => none
      | some api =>
        match hrva : image.plan.layout.importAddressRva? libraryIndex symbolIndex with
        | none => none
        | some rva =>
          match htargets : inputs.targets.get? libraryIndex with
          | none => none
          | some targetLibrary =>
            match htarget : targetLibrary.get? symbolIndex with
            | none => none
            | some target =>
              if hfits : (preferredBase image).toNat + rva < 2 ^ 64 then
              if haddress : observedEA.toNat = (preferredBase image).toNat + rva then
              if hvalue : observedTarget = target then
                some
                  { api
                    libraryIndex, library, libraryLookup := hlibrary
                    libraryName := library.library.name, libraryNameExact := rfl
                    symbolIndex, symbol, symbolLookup := hsymbol
                    symbolNameExact := (apiForBytes?_exact hapi).symm
                    rva, rvaLookup := hrva
                    targetLibrary, targetLibraryLookup := htargets
                    target, targetLookup := htarget
                    addressFits := hfits, addressExact := haddress, targetExact := hvalue }
              else none else none else none

/-- All materialized library/symbol coordinates, in their actual stored order. -/
def candidates (image : ImageInput) : List (Nat × Nat) :=
  image.plan.layout.importLayouts.toList.zipIdx.flatMap fun (library, libraryIndex) =>
    library.library.symbols.toList.zipIdx.map fun (_, symbolIndex) =>
      (libraryIndex, symbolIndex)

/-- Deterministically choose the first actual occurrence satisfying every
layout, name, effective-address, and target check. -/
def select? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs)
    (observedEA observedTarget : BitVec 64) :
    Option (Binding loaded observedEA observedTarget) :=
  (candidates image).findSome? fun candidate =>
    candidateAt? loaded observedEA observedTarget candidate.1 candidate.2

/-- A selected binding pins the request's API constructor through `requestApi`.
The request payload itself remains the existing endpoint-specific model. -/
def Binding.MatchesRequest {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs}
    {observedEA observedTarget : BitVec 64}
    (binding : Binding loaded observedEA observedTarget)
    (request : ApiRequest) : Prop :=
  requestApi request = binding.api

/-- Adapter for an actual successful fixed-form indirect `CALL`.  Its observed
effective address and target are exactly those retained by the receipt. -/
def ofCall? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs)
    {policy : CpuAccessPolicy} {before : State}
    (success : CallFactory.Success policy before) :
    Option (Binding loaded
      (success.receipt.fetch.site.fallthroughRip +
        BitVec.ofInt 64 success.displacement.toInt)
      success.receipt.read.value) :=
  select? loaded
    (success.receipt.fetch.site.fallthroughRip +
      BitVec.ofInt 64 success.displacement.toInt)
    success.receipt.read.value

end Grass.Platform.Win32.ApiDispatch
