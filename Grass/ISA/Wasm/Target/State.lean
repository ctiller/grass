import Grass.ISA.Wasm.Target.Native
import Grass.Target.ISA

/-!
# The whole Wasm machine state, and `step`

Wasm is a stack machine with *structured* control, so unlike a native ISA
there is no fixed "program counter register": `State` carries a call stack
of frames, each with its own instruction index, operand (value) stack, and
*label stack* — the run-time counterpart of `block`/`loop`/`if` nesting.
`br n` does not compute a jump target from an offset encoded in the
instruction (there is none: `Instr.br` carries only a label depth); it reads
the target from the label stack, which is exactly why the label stack has to
be part of `State` and not reconstructed from `Instr` alone.

Every load, store, or data-segment install past the linear memory's declared
length is an `outOfBounds` fault, per `docs/TARGET_SEAMS.md`'s rule that
memory safety is not hidden in the ISA: an unsafe access must get stuck, not
silently succeed, so `Adequate` for a program using this ISA is exactly the
proof that no reachable state performs one.

Known simplifications (see `Native.lean`'s `Fault` docstring and the
per-instruction notes below): `call_indirect` always faults (no table
section is modeled); `memory.grow` always reports failure (`-1`) rather than
growing a fixed-size linear memory. Both are spec-legal responses, not
unsoundness — a program that depends on either succeeding is exactly a
program `Adequate` cannot be proved for on this ISA, which is the intended
diagnostic, not a gap in the model.
-/
namespace Grass.ISA.Wasm.Target

open Grass.ISA.Wasm (Value ValType FuncType)
open Grass.Target (StepOutcome)

/-- A live `block`/`loop`/`if` on a frame's label stack. -/
structure Label where
  /-- Values a branch to this label carries out (0 or 1 in this family). -/
  arity : Nat
  /-- Instruction index a `br` to this label resumes at: for `block`/`if`
  this is just past the matching `end_`; for `loop` it is the `loop`
  instruction's own index, so branching re-enters it and it re-establishes
  a fresh label with a freshly recomputed `exitTarget` — the standard
  "loop-as-its-own-re-entry-point" reading of the spec, without a second
  code path for loop-vs-block branches. -/
  branchTarget : Nat
  /-- Instruction index execution resumes at on falling off this label's
  `end_` normally (always just past it). -/
  exitTarget : Nat
  /-- Operand stack depth when this label was entered; a branch truncates
  back to this depth before pushing its `arity` result values. -/
  stackHeight : Nat
deriving Repr

/-- One call-stack activation. -/
structure Frame where
  functionIndex : Nat
  pc : Nat
  locals : List Value
  valueStack : List Value
  labels : List Label
deriving Repr

/-- The whole machine state. `module` is the program `initial` was called
with: the ISA seam's `step` has no separate access to `Raw`
(`Grass.Target.ISA.step : State → StepOutcome ...`), so the state has to
carry whatever of it execution needs. -/
structure State where
  module : Module
  memory : Nat → Option UInt8
  memoryLength : Nat
  globals : List Value
  /-- Call stack; the head is the currently executing frame. Empty only
  transiently inside a single `step` call (`initial` always produces one
  frame, and returning from the last frame halts instead of emptying it). -/
  frames : List Frame

/-! ## Control-flow scanning

`block`/`loop`/`if` are opened by one instruction and closed by a matching
`end_` in the flat instruction stream (with an optional `else_` inside an
`if`); nesting is tracked at run time by counting further opens/closes, not
looked up from a precomputed table (the seam gives us no separate pass over
`Raw` to build one in — `initial` only builds `State`). Fuel is `body.length`
from the scan's start, which always bounds the number of instructions left
to look at. -/

/-- From just after `body[start]` (a `block`/`loop`/`if`), scan forward to
its matching `end_`, tracking nesting depth, and record the index of a
depth-0 `else_` along the way if one is seen. `none` on a malformed body
(no matching `end_`) — `step` turns that into `Fault.undecodable`. -/
def scanControl (body : List Instr) (start : Nat) : Option (Option Nat × Nat) :=
  let rec go (fuel i depth : Nat) (elseIdx : Option Nat) : Option (Option Nat × Nat) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match body[i]? with
        | none => none
        | some instr =>
            match instr with
            | .block _ | .loop _ | .if_ _ => go fuel (i + 1) (depth + 1) elseIdx
            | .else_ =>
                if depth = 0 then go fuel (i + 1) depth (some i) else go fuel (i + 1) depth elseIdx
            | .end_ =>
                if depth = 0 then some (elseIdx, i) else go fuel (i + 1) (depth - 1) elseIdx
            | _ => go fuel (i + 1) depth elseIdx
  go body.length (start + 1) 0 none

def BlockType.arity : BlockType → Nat
  | .empty => 0
  | .val _ => 1

/-! ## Memory -/

/-- Read `len` consecutive bytes starting at `addr`; `none` as soon as one is
out of bounds (matches `outOfBounds`, not a truncated read). -/
def readBytes (mem : Nat → Option UInt8) (addr len : Nat) : Option (List UInt8) :=
  (List.range len).mapM (fun i => mem (addr + i))

/-- Interpret `bytes` as a little-endian unsigned magnitude, `bytes.head?`
being the least-significant byte (the Wasm binary format's own byte order,
so a memory `Data` segment's bytes and a load/store's bytes use the same
convention). -/
def bytesToNat (bytes : List UInt8) : Nat :=
  bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

def natToBytesLE (n len : Nat) : List UInt8 :=
  (List.range len).map (fun i => UInt8.ofNat ((n / (256 ^ i)) % 256))

def signExtendFrom (value bits : Nat) : Int :=
  if value < 2 ^ (bits - 1) then (value : Int) else (value : Int) - 2 ^ bits

/-- Write `bytes` starting at `addr` into `mem`, as a new memory function.
Bounds are checked by the caller (`doStore`): this helper is total but a
write whose range was never checked against `memoryLength` would silently
extend an in-bounds hole, which is exactly what `doStore` must not do. -/
def writeBytes (mem : Nat → Option UInt8) (addr : Nat) (bytes : List UInt8) : Nat → Option UInt8 :=
  fun a => if addr ≤ a ∧ a < addr + bytes.length then bytes[a - addr]? else mem a

def doLoad (s : State) (base : BitVec 32) (m : MemArg) (byteLen : Nat) (signed : Bool) :
    Option Int :=
  let addr := base.toNat + m.offset
  if addr + byteLen ≤ s.memoryLength then
    (readBytes s.memory addr byteLen).map (fun bytes =>
      let v := bytesToNat bytes
      if signed then signExtendFrom v (byteLen * 8) else (v : Int))
  else none

def doStore (s : State) (base : BitVec 32) (m : MemArg) (byteLen : Nat) (value : Nat) :
    Option (Nat → Option UInt8) :=
  let addr := base.toNat + m.offset
  if addr + byteLen ≤ s.memoryLength then
    some (writeBytes s.memory addr (natToBytesLE value byteLen))
  else none

/-! ## Numeric operators -/

def i32Unary : Instr → BitVec 32 → Except Fault Value
  | .i32Eqz, a => .ok (.i32 (if a = 0 then 1 else 0))
  | .i32Clz, a => .ok (.i32 a.clz)
  | .i32Ctz, a => .ok (.i32 a.ctz)
  | .i32Popcnt, a => .ok (.i32 a.cpop)
  | .i32WrapI64, _ => .error .typeMismatch
  | _, _ => .error .typeMismatch

def i32Binary : Instr → BitVec 32 → BitVec 32 → Except Fault Value
  | .i32Eq, a, b => .ok (.i32 (if a = b then 1 else 0))
  | .i32Ne, a, b => .ok (.i32 (if a ≠ b then 1 else 0))
  | .i32LtS, a, b => .ok (.i32 (if a.slt b then 1 else 0))
  | .i32LtU, a, b => .ok (.i32 (if a.ult b then 1 else 0))
  | .i32GtS, a, b => .ok (.i32 (if b.slt a then 1 else 0))
  | .i32GtU, a, b => .ok (.i32 (if b.ult a then 1 else 0))
  | .i32LeS, a, b => .ok (.i32 (if a.sle b then 1 else 0))
  | .i32LeU, a, b => .ok (.i32 (if a.ule b then 1 else 0))
  | .i32GeS, a, b => .ok (.i32 (if b.sle a then 1 else 0))
  | .i32GeU, a, b => .ok (.i32 (if b.ule a then 1 else 0))
  | .i32Add, a, b => .ok (.i32 (a + b))
  | .i32Sub, a, b => .ok (.i32 (a - b))
  | .i32Mul, a, b => .ok (.i32 (a * b))
  | .i32DivS, a, b =>
      if b = 0 then .error .divideByZero
      else if BitVec.sdivOverflow a b then .error .integerOverflow
      else .ok (.i32 (BitVec.sdiv a b))
  | .i32DivU, a, b => if b = 0 then .error .divideByZero else .ok (.i32 (BitVec.udiv a b))
  | .i32RemS, a, b => if b = 0 then .error .divideByZero else .ok (.i32 (BitVec.srem a b))
  | .i32RemU, a, b => if b = 0 then .error .divideByZero else .ok (.i32 (BitVec.umod a b))
  | .i32And, a, b => .ok (.i32 (a &&& b))
  | .i32Or, a, b => .ok (.i32 (a ||| b))
  | .i32Xor, a, b => .ok (.i32 (a ^^^ b))
  | .i32Shl, a, b => .ok (.i32 (a <<< (b.toNat % 32)))
  | .i32ShrS, a, b => .ok (.i32 (a.sshiftRight (b.toNat % 32)))
  | .i32ShrU, a, b => .ok (.i32 (a >>> (b.toNat % 32)))
  | .i32Rotl, a, b => .ok (.i32 (a.rotateLeft b.toNat))
  | .i32Rotr, a, b => .ok (.i32 (a.rotateRight b.toNat))
  | _, _, _ => .error .typeMismatch

def i64Unary : Instr → BitVec 64 → Except Fault Value
  | .i64Eqz, a => .ok (.i32 (if a = 0 then 1 else 0))
  | .i64Clz, a => .ok (.i64 a.clz)
  | .i64Ctz, a => .ok (.i64 a.ctz)
  | .i64Popcnt, a => .ok (.i64 a.cpop)
  | .i32WrapI64, a => .ok (.i32 (BitVec.ofNat 32 a.toNat))
  | .i64ExtendI32S, _ => .error .typeMismatch
  | .i64ExtendI32U, _ => .error .typeMismatch
  | _, _ => .error .typeMismatch

def i64Binary : Instr → BitVec 64 → BitVec 64 → Except Fault Value
  | .i64Eq, a, b => .ok (.i32 (if a = b then 1 else 0))
  | .i64Ne, a, b => .ok (.i32 (if a ≠ b then 1 else 0))
  | .i64LtS, a, b => .ok (.i32 (if a.slt b then 1 else 0))
  | .i64LtU, a, b => .ok (.i32 (if a.ult b then 1 else 0))
  | .i64GtS, a, b => .ok (.i32 (if b.slt a then 1 else 0))
  | .i64GtU, a, b => .ok (.i32 (if b.ult a then 1 else 0))
  | .i64LeS, a, b => .ok (.i32 (if a.sle b then 1 else 0))
  | .i64LeU, a, b => .ok (.i32 (if a.ule b then 1 else 0))
  | .i64GeS, a, b => .ok (.i32 (if b.sle a then 1 else 0))
  | .i64GeU, a, b => .ok (.i32 (if b.ule a then 1 else 0))
  | .i64Add, a, b => .ok (.i64 (a + b))
  | .i64Sub, a, b => .ok (.i64 (a - b))
  | .i64Mul, a, b => .ok (.i64 (a * b))
  | .i64DivS, a, b =>
      if b = 0 then .error .divideByZero
      else if BitVec.sdivOverflow a b then .error .integerOverflow
      else .ok (.i64 (BitVec.sdiv a b))
  | .i64DivU, a, b => if b = 0 then .error .divideByZero else .ok (.i64 (BitVec.udiv a b))
  | .i64RemS, a, b => if b = 0 then .error .divideByZero else .ok (.i64 (BitVec.srem a b))
  | .i64RemU, a, b => if b = 0 then .error .divideByZero else .ok (.i64 (BitVec.umod a b))
  | .i64And, a, b => .ok (.i64 (a &&& b))
  | .i64Or, a, b => .ok (.i64 (a ||| b))
  | .i64Xor, a, b => .ok (.i64 (a ^^^ b))
  | .i64Shl, a, b => .ok (.i64 (a <<< (b.toNat % 64)))
  | .i64ShrS, a, b => .ok (.i64 (a.sshiftRight (b.toNat % 64)))
  | .i64ShrU, a, b => .ok (.i64 (a >>> (b.toNat % 64)))
  | .i64Rotl, a, b => .ok (.i64 (a.rotateLeft b.toNat))
  | .i64Rotr, a, b => .ok (.i64 (a.rotateRight b.toNat))
  | _, _, _ => .error .typeMismatch

def i64ExtendFromI32 : Instr → BitVec 32 → Except Fault Value
  | .i64ExtendI32S, a => .ok (.i64 (BitVec.ofInt 64 a.toInt))
  | .i64ExtendI32U, a => .ok (.i64 (BitVec.ofNat 64 a.toNat))
  | _, _ => .error .typeMismatch

/-! ## Frame helpers -/

def Frame.pop1 (f : Frame) : Option (Value × Frame) :=
  match f.valueStack with
  | v :: rest => some (v, { f with valueStack := rest })
  | [] => none

/-- `a` is the first (lower) operand, `b` the second (upper, top-of-stack)
operand — Wasm's own binop order, `a b op` pushes `a` then `b`. -/
def Frame.pop2 (f : Frame) : Option (Value × Value × Frame) :=
  match f.valueStack with
  | b :: a :: rest => some (a, b, { f with valueStack := rest })
  | _ => none

def Frame.push (f : Frame) (v : Value) : Frame := { f with valueStack := v :: f.valueStack }

def Frame.next (f : Frame) : Frame := { f with pc := f.pc + 1 }

/-! ## `step` -/

/-- Unwind the current frame, delivering its top `resultCount` values to the
caller (or halting if there is no caller): shared by an explicit `return_`
and by falling off the end of a function body, which the spec treats the
same way. -/
def returnFrom (s : State) (results : List Value) (callerFrames : List Frame) :
    StepOutcome State NativeCall NativeReturn Fault :=
  match callerFrames with
  | [] => .halted
  | caller :: rest =>
      .internal { s with frames := { caller with valueStack := results ++ caller.valueStack }.next :: rest }

/-- `br n`: read the target label (`n` levels up the current frame's label
stack), carry its `arity` result values out, discard everything above the
label's entry stack depth, and resume at its `branchTarget`. -/
def doBranch (s : State) (frame : Frame) (callerFrames : List Frame) (n : Nat) :
    StepOutcome State NativeCall NativeReturn Fault :=
  match frame.labels[n]? with
  | none => .fault .undecodable
  | some label =>
      let results := frame.valueStack.take label.arity
      let below :=
        if label.stackHeight ≤ frame.valueStack.length then
          frame.valueStack.drop (frame.valueStack.length - label.stackHeight)
        else frame.valueStack
      let newFrame : Frame :=
        { frame with
          valueStack := results ++ below
          labels := frame.labels.drop (n + 1)
          pc := label.branchTarget }
      .internal { s with frames := newFrame :: callerFrames }

/-- Begin a call to function `funcIdx`, whose signature is `ft`: split the
argument values off the caller's stack, then either push a fresh frame (a
defined callee) or hand the platform a `NativeCall` (an imported callee).
Shared by `call` and — were a table modeled — what `call_indirect` would do
once it resolved to a concrete index.

A native return's memory writes are masked back to `memoryLength` for the
same reason `buildMemory` masks data segments: `writeBytes` is total, so an
unmasked platform write past the declared size would create addressable
bytes outside linear memory. A platform whose answer names an out-of-range
buffer therefore loses those bytes rather than growing the machine's memory
— see this file's report on the missing `NativeReturn` failure channel. -/
def beginCall (s : State) (frame : Frame) (callerFrames : List Frame) (funcIdx : Nat)
    (ft : FuncType) : StepOutcome State NativeCall NativeReturn Fault :=
  let nargs := ft.params.length
  if nargs ≤ frame.valueStack.length then
    let args := (frame.valueStack.take nargs).reverse
    let remaining := frame.valueStack.drop nargs
    let caller := { frame with valueStack := remaining }.next
    if funcIdx < s.module.imports.length then
      match s.module.imports[funcIdx]? with
      | none => .fault .undecodable
      | some imp =>
          let call : NativeCall :=
            { importIndex := funcIdx
              moduleName := imp.moduleName
              fieldName := imp.fieldName
              args := args
              read := fun addr len => readBytes s.memory addr len }
          let resume : NativeReturn → State := fun ret =>
            let written := ret.writes.foldl (fun mem (addr, bytes) => writeBytes mem addr bytes) s.memory
            let memory' : Nat → Option UInt8 :=
              fun a => if a < s.memoryLength then written a else none
            { s with
              memory := memory'
              frames := { caller with valueStack := ret.results.reverse ++ caller.valueStack } :: callerFrames }
          .external call resume
    else
      match s.module.functionBody funcIdx with
      | none => .fault .undecodable
      | some callee =>
          let locals := args ++ callee.locals.map ValType.zero
          let newFrame : Frame := ⟨funcIdx, 0, locals, [], []⟩
          .internal { s with frames := newFrame :: caller :: callerFrames }
  else .fault .stackExhausted

set_option maxHeartbeats 1000000 in
/-- One instruction. `Instr` is the whole flat MVP integer opcode set
(`Target/Instr.lean`); this covers every constructor in it — the numeric,
memory, and variable-access instructions computationally, `block`/`loop`/
`if`/`else_`/`end_`/`br`/`brIf`/`brTable`/`return_`/`call` through the
label-stack and call-stack machinery above, `call_indirect` and
`memory.grow` as documented, always-fails faults/responses (no table, no
resizable memory modeled — see the file docstring). -/
def step (s : State) : StepOutcome State NativeCall NativeReturn Fault :=
  match s.frames with
  | [] => .fault .stackExhausted
  | frame :: callerFrames =>
    match s.module.functionBody frame.functionIndex with
    | none => .fault .undecodable
    | some func =>
      match func.body[frame.pc]? with
      | none =>
          match s.module.funcTypeOf frame.functionIndex with
          | none => .fault .undecodable
          | some ft => returnFrom s (frame.valueStack.take ft.results.length) callerFrames
      | some instr =>
        match instr with
        | .unreachable => .fault .unreachable
        | .nop => .internal { s with frames := frame.next :: callerFrames }
        | .drop =>
            match frame.pop1 with
            | none => .fault .stackExhausted
            | some (_, f) => .internal { s with frames := f.next :: callerFrames }
        | .select =>
            match frame.valueStack with
            | .i32 c :: b :: a :: rest =>
                let result := if c ≠ 0 then a else b
                .internal { s with frames := { frame with valueStack := result :: rest }.next :: callerFrames }
            | _ => .fault .typeMismatch
        | .block bt =>
            match scanControl func.body frame.pc with
            | none => .fault .undecodable
            | some (_, endIdx) =>
                let label : Label := ⟨bt.arity, endIdx + 1, endIdx + 1, frame.valueStack.length⟩
                let newFrame := { frame with pc := frame.pc + 1, labels := label :: frame.labels }
                .internal { s with frames := newFrame :: callerFrames }
        | .loop bt =>
            match scanControl func.body frame.pc with
            | none => .fault .undecodable
            | some (_, endIdx) =>
                let label : Label := ⟨bt.arity, frame.pc, endIdx + 1, frame.valueStack.length⟩
                let newFrame := { frame with pc := frame.pc + 1, labels := label :: frame.labels }
                .internal { s with frames := newFrame :: callerFrames }
        | .if_ bt =>
            match frame.pop1 with
            | none => .fault .stackExhausted
            | some (.i32 c, f) =>
                match scanControl func.body frame.pc with
                | none => .fault .undecodable
                | some (elseIdx, endIdx) =>
                    let label : Label := ⟨bt.arity, endIdx + 1, endIdx + 1, f.valueStack.length⟩
                    if c ≠ 0 then
                      .internal { s with frames := { f with pc := frame.pc + 1, labels := label :: f.labels } :: callerFrames }
                    else
                      match elseIdx with
                      | some ei => .internal { s with frames := { f with pc := ei + 1, labels := label :: f.labels } :: callerFrames }
                      | none => .internal { s with frames := { f with pc := endIdx + 1 } :: callerFrames }
            | some _ => .fault .typeMismatch
        | .else_ =>
            match frame.labels with
            | [] => .fault .undecodable
            | label :: rest =>
                .internal { s with frames := { frame with pc := label.exitTarget, labels := rest } :: callerFrames }
        | .end_ =>
            match frame.labels with
            | [] =>
                match s.module.funcTypeOf frame.functionIndex with
                | none => .fault .undecodable
                | some ft => returnFrom s (frame.valueStack.take ft.results.length) callerFrames
            | _ :: rest => .internal { s with frames := { frame with pc := frame.pc + 1, labels := rest } :: callerFrames }
        | .br n => doBranch s frame callerFrames n
        | .brIf n =>
            match frame.pop1 with
            | none => .fault .stackExhausted
            | some (.i32 c, f) => if c ≠ 0 then doBranch s f callerFrames n else .internal { s with frames := f.next :: callerFrames }
            | some _ => .fault .typeMismatch
        | .brTable labels default =>
            match frame.pop1 with
            | none => .fault .stackExhausted
            | some (.i32 idx, f) => doBranch s f callerFrames (labels.getD idx.toNat default)
            | some _ => .fault .typeMismatch
        | .return_ =>
            match s.module.funcTypeOf frame.functionIndex with
            | none => .fault .undecodable
            | some ft => returnFrom s (frame.valueStack.take ft.results.length) callerFrames
        | .call funcIdx =>
            match s.module.funcTypeOf funcIdx with
            | none => .fault .undecodable
            | some ft => beginCall s frame callerFrames funcIdx ft
        | .callIndirect _ _ => .fault .undecodable
        | .localGet i =>
            match frame.locals[i]? with
            | none => .fault .undecodable
            | some v => .internal { s with frames := (frame.push v).next :: callerFrames }
        | .localSet i =>
            match frame.pop1 with
            | none => .fault .stackExhausted
            | some (v, f) =>
                if i < f.locals.length then
                  .internal { s with frames := { f with locals := f.locals.set i v }.next :: callerFrames }
                else .fault .undecodable
        | .localTee i =>
            match frame.valueStack with
            | v :: _ =>
                if i < frame.locals.length then
                  .internal { s with frames := { frame with locals := frame.locals.set i v }.next :: callerFrames }
                else .fault .undecodable
            | [] => .fault .stackExhausted
        | .globalGet i =>
            match s.globals[i]? with
            | none => .fault .undecodable
            | some v => .internal { s with frames := (frame.push v).next :: callerFrames }
        | .globalSet i =>
            match frame.pop1, s.module.globals[i]? with
            | none, _ => .fault .stackExhausted
            | _, none => .fault .undecodable
            | some (v, f), some g =>
                if g.mutable then
                  .internal { s with globals := s.globals.set i v, frames := f.next :: callerFrames }
                else .fault .typeMismatch
        -- Memory
        | .i32Load m | .i32Load8S m | .i32Load8U m | .i32Load16S m | .i32Load16U m
        | .i64Load m | .i64Load8S m | .i64Load8U m | .i64Load16S m | .i64Load16U m
        | .i64Load32S m | .i64Load32U m =>
            match frame.pop1 with
            | none => .fault .stackExhausted
            | some (.i32 base, f) =>
                let (byteLen, signed, wide) : Nat × Bool × Bool :=
                  match instr with
                  | .i32Load _ => (4, false, false)
                  | .i32Load8S _ => (1, true, false)
                  | .i32Load8U _ => (1, false, false)
                  | .i32Load16S _ => (2, true, false)
                  | .i32Load16U _ => (2, false, false)
                  | .i64Load _ => (8, false, true)
                  | .i64Load8S _ => (1, true, true)
                  | .i64Load8U _ => (1, false, true)
                  | .i64Load16S _ => (2, true, true)
                  | .i64Load16U _ => (2, false, true)
                  | .i64Load32S _ => (4, true, true)
                  | .i64Load32U _ => (4, false, true)
                  | _ => (0, false, false)
                match doLoad s base m byteLen signed with
                | none => .fault .outOfBounds
                | some v =>
                    let result : Value := if wide then .i64 (BitVec.ofInt 64 v) else .i32 (BitVec.ofInt 32 v)
                    .internal { s with frames := (f.push result).next :: callerFrames }
            | some _ => .fault .typeMismatch
        | .i32Store m | .i32Store8 m | .i32Store16 m
        | .i64Store m | .i64Store8 m | .i64Store16 m | .i64Store32 m =>
            match frame.pop2 with
            | none => .fault .stackExhausted
            | some (.i32 base, value, f) =>
                let byteLenAndValue : Option (Nat × Nat) :=
                  match instr, value with
                  | .i32Store _, .i32 v => some (4, v.toNat)
                  | .i32Store8 _, .i32 v => some (1, v.toNat)
                  | .i32Store16 _, .i32 v => some (2, v.toNat)
                  | .i64Store _, .i64 v => some (8, v.toNat)
                  | .i64Store8 _, .i64 v => some (1, v.toNat)
                  | .i64Store16 _, .i64 v => some (2, v.toNat)
                  | .i64Store32 _, .i64 v => some (4, v.toNat)
                  | _, _ => none
                match byteLenAndValue with
                | none => .fault .typeMismatch
                | some (byteLen, natValue) =>
                    match doStore s base m byteLen natValue with
                    | none => .fault .outOfBounds
                    | some mem' => .internal { s with memory := mem', frames := f.next :: callerFrames }
            | some _ => .fault .typeMismatch
        | .memorySize => .internal { s with frames := (frame.push (.i32 (BitVec.ofNat 32 (s.memoryLength / 65536)))).next :: callerFrames }
        | .memoryGrow =>
            match frame.pop1 with
            | none => .fault .stackExhausted
            | some (.i32 _, f) => .internal { s with frames := (f.push (.i32 (BitVec.ofInt 32 (-1)))).next :: callerFrames }
            | some _ => .fault .typeMismatch
        -- Constants
        | .i32Const v => .internal { s with frames := (frame.push (.i32 v)).next :: callerFrames }
        | .i64Const v => .internal { s with frames := (frame.push (.i64 v)).next :: callerFrames }
        -- Unary numeric
        | .i32Eqz | .i32Clz | .i32Ctz | .i32Popcnt =>
            match frame.pop1 with
            | some (.i32 a, f) =>
                match i32Unary instr a with
                | .error e => .fault e
                | .ok v => .internal { s with frames := (f.push v).next :: callerFrames }
            | some _ => .fault .typeMismatch
            | none => .fault .stackExhausted
        | .i64Eqz | .i64Clz | .i64Ctz | .i64Popcnt =>
            match frame.pop1 with
            | some (.i64 a, f) =>
                match i64Unary instr a with
                | .error e => .fault e
                | .ok v => .internal { s with frames := (f.push v).next :: callerFrames }
            | some _ => .fault .typeMismatch
            | none => .fault .stackExhausted
        | .i32WrapI64 =>
            match frame.pop1 with
            | some (.i64 a, f) =>
                match i64Unary .i32WrapI64 a with
                | .error e => .fault e
                | .ok v => .internal { s with frames := (f.push v).next :: callerFrames }
            | some _ => .fault .typeMismatch
            | none => .fault .stackExhausted
        | .i64ExtendI32S | .i64ExtendI32U =>
            match frame.pop1 with
            | some (.i32 a, f) =>
                match i64ExtendFromI32 instr a with
                | .error e => .fault e
                | .ok v => .internal { s with frames := (f.push v).next :: callerFrames }
            | some _ => .fault .typeMismatch
            | none => .fault .stackExhausted
        -- Binary i32 numeric (arithmetic and comparisons)
        | .i32Eq | .i32Ne | .i32LtS | .i32LtU | .i32GtS | .i32GtU | .i32LeS | .i32LeU
        | .i32GeS | .i32GeU | .i32Add | .i32Sub | .i32Mul | .i32DivS | .i32DivU | .i32RemS
        | .i32RemU | .i32And | .i32Or | .i32Xor | .i32Shl | .i32ShrS | .i32ShrU | .i32Rotl
        | .i32Rotr =>
            match frame.pop2 with
            | some (.i32 a, .i32 b, f) =>
                match i32Binary instr a b with
                | .error e => .fault e
                | .ok v => .internal { s with frames := (f.push v).next :: callerFrames }
            | some _ => .fault .typeMismatch
            | none => .fault .stackExhausted
        -- Binary i64 numeric (arithmetic and comparisons)
        | .i64Eq | .i64Ne | .i64LtS | .i64LtU | .i64GtS | .i64GtU | .i64LeS | .i64LeU
        | .i64GeS | .i64GeU | .i64Add | .i64Sub | .i64Mul | .i64DivS | .i64DivU | .i64RemS
        | .i64RemU | .i64And | .i64Or | .i64Xor | .i64Shl | .i64ShrS | .i64ShrU | .i64Rotl
        | .i64Rotr =>
            match frame.pop2 with
            | some (.i64 a, .i64 b, f) =>
                match i64Binary instr a b with
                | .error e => .fault e
                | .ok v => .internal { s with frames := (f.push v).next :: callerFrames }
            | some _ => .fault .typeMismatch
            | none => .fault .stackExhausted

/-- Install a module's data segments and any platform-supplied bytes
(`ctx.initialMemory`) into a zero-initialized linear memory of the module's
declared size. Platform bytes are installed first so a module's own data
segments can legitimately overlap/override the region a loader reserved for
them (mirrors how an ELF/PE loader lays out the image before its own
relocations run).

`writeBytes` is total, so an install past `memoryBytes` would *create*
addressable bytes outside linear memory and make an out-of-bounds read
succeed. That is why `initial` refuses to start a machine whose installs do
not fit (`instantiates`): this function is only ever reached for a layout
that stays inside the declared size. -/
def buildMemory (m : Module) (ctx : InitialContext) : Nat → Option UInt8 :=
  let base : Nat → Option UInt8 := fun a => if a < m.memoryBytes then some 0 else none
  let withCtx := ctx.initialMemory.foldl (fun mem (addr, bytes) => writeBytes mem addr bytes) base
  m.data.foldl (fun mem d => writeBytes mem d.offset d.bytes) withCtx

/-- Whether every byte `buildMemory` would install — the module's data
segments and the platform's `initialMemory` — lands inside the declared
linear memory. Wasm instantiation traps when a data segment does not fit;
`initial` is total, so it reports the trap by starting the machine at an
unresolvable function instead. -/
def instantiates (m : Module) (ctx : InitialContext) : Bool :=
  m.data.all (fun d => d.offset + d.bytes.length ≤ m.memoryBytes) &&
    ctx.initialMemory.all (fun p => p.1 + p.2.length ≤ m.memoryBytes)

/-- The function index a context's entry export resolves to, or
`Module.unresolvedIndex` when the module exports no such name or the initial
memory layout does not fit. Only `initial` sees both the module and the
context, so this is the only place the entry name can be resolved
(`InitialContext`'s docstring). -/
def entryIndex (m : Module) (ctx : InitialContext) : Nat :=
  if instantiates m ctx then (m.exportedFunc ctx.startExport).getD m.unresolvedIndex
  else m.unresolvedIndex

/-- The loaded initial state: the entry export's frame, globals at their
initializers, and linear memory as built by `buildMemory`. An
`InitialContext` naming an export this module does not resolve, and a module
whose data segments overrun its declared linear memory, both still produce a
total `State` — one whose frame sits past the function index space, so the
very first `step` faults `undecodable` (`step_initial_of_unresolved`,
`step_initial_of_overflow`) rather than the seam's `initial` needing to be
partial or defaulting to function `0`. -/
def initial (m : Module) (ctx : InitialContext) : State :=
  let index := entryIndex m ctx
  let locals :=
    match m.functionBody index with
    | none => []
    | some f =>
        match m.funcTypeOf index with
        | none => []
        | some ft => ft.params.map ValType.zero ++ f.locals.map ValType.zero
  { module := m
    memory := buildMemory m ctx
    memoryLength := m.memoryBytes
    globals := m.globals.map Global.init
    frames := [⟨index, 0, locals, [], []⟩] }

/-- A machine started past the function index space gets stuck immediately.
Shared by the two refusals below. -/
private theorem step_initial_of_unresolvedIndex (m : Module) (ctx : InitialContext)
    (index : entryIndex m ctx = m.unresolvedIndex) :
    step (initial m ctx) = .fault .undecodable := by
  have body : m.functionBody (entryIndex m ctx) = none := by
    rw [index]
    simp [Module.functionBody, Module.unresolvedIndex]
  simp [step, initial, body]

/-- An unresolvable entry export gets stuck immediately: the first `step`
faults. This is the refusal that replaces guessing function `0`. -/
theorem step_initial_of_unresolved (m : Module) (ctx : InitialContext)
    (unresolved : m.exportedFunc ctx.startExport = none) :
    step (initial m ctx) = .fault .undecodable :=
  step_initial_of_unresolvedIndex m ctx (by simp [entryIndex, unresolved])

/-- An initial memory layout that overruns the declared linear memory gets
stuck immediately, whatever the module exports: Wasm instantiation traps,
and a total `initial` reports that trap as a machine that cannot take a
step. Without this refusal `buildMemory`'s total `writeBytes` would create
addressable bytes outside linear memory and an out-of-bounds read would
succeed. -/
theorem step_initial_of_overflow (m : Module) (ctx : InitialContext)
    (overflow : instantiates m ctx = false) :
    step (initial m ctx) = .fault .undecodable :=
  step_initial_of_unresolvedIndex m ctx (by simp [entryIndex, overflow])

end Grass.ISA.Wasm.Target
