import Grass.CFG.Stack

/-!
# Abstract stack-shape fixtures

These fixtures cover balanced depth changes, underflow refusal, alignment
requirements, fresh lexical scopes, LIFO elimination, and exact edge shape
compatibility.
-/

namespace Grass.Tests.CFG.Stack

open Grass Grass.CFG

def scope (name : String) : StackScopeId := ⟨⟨"test.stack", name⟩⟩

def localScope := scope "local"
def nested := scope "nested"

def base : StackShape := .empty
def reserve32 : StackDelta := ⟨0, 32⟩
def release32 : StackDelta := ⟨32, 0⟩

example : reserve32.apply? base = some ⟨32, []⟩ := by decide
example : release32.apply? base = none := by decide
example : release32.apply? ⟨32, []⟩ = some base := by decide

example (after : StackShape) (h : reserve32.apply? base = some after) :
    after.openScopes = base.openScopes :=
  StackDelta.apply?_openScopes reserve32 base after h

example (after : StackShape) (h : reserve32.apply? base = some after) :
    after.depth = base.depth - reserve32.release + reserve32.reserve :=
  StackDelta.apply?_depth reserve32 base after h

example (after : StackShape) (h : reserve32.apply? base = some after) :
    after.WellFormed :=
  StackDelta.apply?_wellFormed reserve32 base after (by decide) h

def aligned16 : StackAlignment := ⟨16, 0⟩
def callAligned16 : StackAlignment := ⟨16, 8⟩

example : aligned16.wellFormed := by decide
example : aligned16.accepts ⟨32, []⟩ := by decide
example : callAligned16.accepts ⟨40, []⟩ := by decide
example : ¬ callAligned16.accepts ⟨32, []⟩ := by decide
example : ¬ (StackAlignment.mk 0 0).wellFormed := by decide
example : ¬ (StackAlignment.mk 8 8).wellFormed := by decide

def withLocal : StackShape := ⟨32, [localScope]⟩
def withNested : StackShape := ⟨32, [nested, localScope]⟩

example : base.enterScope? localScope = some ⟨0, [localScope]⟩ := by decide
example : withLocal.enterScope? nested = some withNested := by decide
example : withLocal.enterScope? localScope = none := by decide
example : withNested.leaveScope? nested = some withLocal := by decide
example : withNested.leaveScope? localScope = none := by decide
example : base.leaveScope? localScope = none := by decide

example (entered : StackShape) (h : withLocal.enterScope? nested = some entered) :
    entered.leaveScope? nested = some withLocal :=
  StackShape.leaveScope?_enterScope? withLocal entered nested h

example (entered : StackShape) (h : withLocal.enterScope? nested = some entered) :
    entered.WellFormed :=
  StackShape.enterScope?_wellFormed withLocal entered nested (by decide) h

example (left : StackShape) (h : withNested.leaveScope? nested = some left) :
    left.WellFormed :=
  StackShape.leaveScope?_wellFormed withNested left nested (by decide) h

example : withNested.WellFormed := by decide
example : ¬ (StackShape.mk 32 [localScope, localScope]).WellFormed := by decide

example : withLocal.compatible withLocal := by decide
example : ¬ withLocal.compatible ⟨32, []⟩ := by decide
example : ¬ withLocal.compatible ⟨16, [localScope]⟩ := by decide

end Grass.Tests.CFG.Stack
