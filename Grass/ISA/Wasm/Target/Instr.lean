import Grass.ISA.Wasm.Types

/-!
# One Wasm instruction

Wasm is a stack machine with *structured* control: `block`/`loop`/`if`/`else`
are themselves instructions in the flat binary instruction stream, closed by
an explicit `end`. `Instr` is therefore one instruction of that flat stream,
matching `Grass.Target.ISA.Instr` exactly: nesting is not a type-level
property here, it is a run-time property of how `State.step` tracks a label
stack over instruction indices (`Grass/ISA/Wasm/Target/State.lean`).

This is the MVP integer subset: no reference types, no vectors, no floats.
`ValType`/`Value` are reused from `Grass.ISA.Wasm.Types` rather than
redeclared.
-/
namespace Grass.ISA.Wasm.Target

open Grass.ISA.Wasm (ValType)

/-- The result-type annotation on `block`/`loop`/`if`. The restricted value
universe (no reference or vector types) makes this exactly a single optional
`ValType`, never the general type-index form the full Core spec allows. -/
inductive BlockType where
  | empty
  | val (t : ValType)
deriving DecidableEq, Repr

/-- The alignment hint and byte offset carried by every memory instruction. -/
structure MemArg where
  align : Nat
  offset : Nat
deriving DecidableEq, Repr

/-- One instruction of the flat Wasm binary instruction stream. -/
inductive Instr where
  -- Control
  | unreachable
  | nop
  | block (bt : BlockType)
  | loop (bt : BlockType)
  | if_ (bt : BlockType)
  | else_
  | end_
  | br (label : Nat)
  | brIf (label : Nat)
  | brTable (labels : List Nat) (default : Nat)
  | return_
  | call (func : Nat)
  | callIndirect (type table : Nat)
  -- Parametric
  | drop
  | select
  -- Variable
  | localGet (index : Nat)
  | localSet (index : Nat)
  | localTee (index : Nat)
  | globalGet (index : Nat)
  | globalSet (index : Nat)
  -- Memory
  | i32Load (m : MemArg)
  | i64Load (m : MemArg)
  | i32Load8S (m : MemArg)
  | i32Load8U (m : MemArg)
  | i32Load16S (m : MemArg)
  | i32Load16U (m : MemArg)
  | i64Load8S (m : MemArg)
  | i64Load8U (m : MemArg)
  | i64Load16S (m : MemArg)
  | i64Load16U (m : MemArg)
  | i64Load32S (m : MemArg)
  | i64Load32U (m : MemArg)
  | i32Store (m : MemArg)
  | i64Store (m : MemArg)
  | i32Store8 (m : MemArg)
  | i32Store16 (m : MemArg)
  | i64Store8 (m : MemArg)
  | i64Store16 (m : MemArg)
  | i64Store32 (m : MemArg)
  | memorySize
  | memoryGrow
  -- Numeric constants
  | i32Const (value : BitVec 32)
  | i64Const (value : BitVec 64)
  -- i32 comparisons
  | i32Eqz | i32Eq | i32Ne | i32LtS | i32LtU | i32GtS | i32GtU
  | i32LeS | i32LeU | i32GeS | i32GeU
  -- i64 comparisons
  | i64Eqz | i64Eq | i64Ne | i64LtS | i64LtU | i64GtS | i64GtU
  | i64LeS | i64LeU | i64GeS | i64GeU
  -- i32 arithmetic
  | i32Clz | i32Ctz | i32Popcnt | i32Add | i32Sub | i32Mul | i32DivS | i32DivU
  | i32RemS | i32RemU | i32And | i32Or | i32Xor | i32Shl | i32ShrS | i32ShrU
  | i32Rotl | i32Rotr
  -- i64 arithmetic
  | i64Clz | i64Ctz | i64Popcnt | i64Add | i64Sub | i64Mul | i64DivS | i64DivU
  | i64RemS | i64RemU | i64And | i64Or | i64Xor | i64Shl | i64ShrS | i64ShrU
  | i64Rotl | i64Rotr
  -- Conversions
  | i32WrapI64
  | i64ExtendI32S
  | i64ExtendI32U
deriving DecidableEq, Repr

end Grass.ISA.Wasm.Target
