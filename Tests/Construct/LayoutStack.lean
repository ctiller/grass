import Grass.Construct.Layout.Stack
import Tests.Construct.LayoutCore

/-!
# Lexical stack layout fixtures

Fixtures pin nested scope order and fixed object ranges, then reject overlap,
undeclared scopes, duplicate names, oversize frames, escaping addresses, live
loans, and live obligations.
-/

namespace Grass.Tests.Construct.LayoutStack

open Grass Grass.Core Grass.Construct.Layout
open Grass.Tests.Construct.LayoutCore

def scope (name : String) : ScopeId := ⟨⟨name⟩⟩

def word : ObjectRepr profile := ⟨8, 8⟩

def layout : StackLayout profile where
  scopes := [⟨scope "root", none⟩, ⟨scope "child", some (scope "root")⟩]
  objects := [
    ⟨⟨"counter"⟩, word, 0, scope "root"⟩,
    ⟨⟨"scratch"⟩, word, 8, scope "child"⟩
  ]
  size := 16
  alignment := 8
  maxSize := 64

example : layout.WellFormed := by native_decide
example : layout.objects.map (fun object => object.byteRange) = [⟨0, 8⟩, ⟨8, 8⟩] :=
  by native_decide

def overlapping : StackLayout profile :=
  { layout with objects := [
      ⟨⟨"counter"⟩, word, 0, scope "root"⟩,
      ⟨⟨"scratch"⟩, word, 4, scope "child"⟩
    ] }

example : ¬ overlapping.WellFormed := by native_decide

def undeclared : StackLayout profile :=
  { layout with objects := [
      ⟨⟨"counter"⟩, word, 0, scope "missing"⟩
    ] }

example : ¬ undeclared.WellFormed := by native_decide

def duplicate : StackLayout profile :=
  { layout with objects := [
      ⟨⟨"counter"⟩, word, 0, scope "root"⟩,
      ⟨⟨"counter"⟩, word, 8, scope "child"⟩
    ] }

example : ¬ duplicate.WellFormed := by native_decide

def oversized : StackLayout profile := { layout with size := 72 }
example : ¬ oversized.WellFormed := by native_decide

def closed : ScopeExit String := ⟨[], [], []⟩
def escaping : ScopeExit String := ⟨[⟨"counter"⟩], [], []⟩
def loaned : ScopeExit String := ⟨[], ["loan"], []⟩
def obligated : ScopeExit String := ⟨[], [], ["restore"]⟩

example : closed.WellFormed := by native_decide
example : ¬ escaping.WellFormed := by native_decide
example : ¬ loaned.WellFormed := by native_decide
example : ¬ obligated.WellFormed := by native_decide

end Grass.Tests.Construct.LayoutStack
