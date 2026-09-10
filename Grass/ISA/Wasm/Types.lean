import Std

/-!
Integer value and function-signature vocabulary for the initial Wasm family.
This is an explicitly restricted Core 2.0 family, not a whole-Core validator.
Authority: WebAssembly Core 2.0, Syntax/Values and Syntax/Types:
https://www.w3.org/TR/wasm-core-2/ . Runtime store addresses below are logical
indices, never native pointers or linear-memory addresses.
-/
namespace Grass.ISA.Wasm

inductive ValType where
  | i32
  | i64
deriving DecidableEq, Repr

inductive Value where
  | i32 (bits : BitVec 32)
  | i64 (bits : BitVec 64)
deriving DecidableEq, Repr

def Value.type : Value → ValType
  | .i32 _ => .i32
  | .i64 _ => .i64

def ValType.zero : ValType → Value
  | .i32 => .i32 0
  | .i64 => .i64 0

@[simp] theorem ValType.zero_type (t : ValType) : t.zero.type = t := by
  cases t <;> rfl

structure FuncType where
  params : List ValType
  results : List ValType
deriving DecidableEq, Repr

/-- Runtime store identity; distinct from a module-local function index. -/
structure FuncAddr where
  index : Nat
deriving DecidableEq, Repr

structure ModuleAddr where
  index : Nat
deriving DecidableEq, Repr

/-- Identity of an external host function in the selected runtime model.
It supplies no evidence of the host's behavior or native implementation. -/
structure HostId where
  index : Nat
deriving DecidableEq, Repr

end Grass.ISA.Wasm
