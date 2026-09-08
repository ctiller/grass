import Grass.Unsafe.Construct

/-!
# Raw hierarchy emission

This module streams explicitly tainted raw byte chunks through a caller-owned
writer. It does not define filesystem or artifact authority and does not claim
that a successful callback persisted anything. `emit_state` pins the exact
ordered `ByteSeq` inputs supplied to that callback, while the returned receipt
retains the input lists and every chunk's taint for inspection.
-/

namespace Grass.Unsafe.Emit

open Grass Grass.Std.Logical Grass.Unsafe

/-- One concrete writer input paired with its nonempty missing-check account. -/
structure Chunk where
  bytes : ByteSeq
  taint : Taint
deriving Repr, DecidableEq

namespace Chunk

/-- Convert approved raw bytes to an emission chunk without changing data or taint. -/
def ofRaw (raw : Unsafe.Construct.Bytes) : Chunk :=
  ⟨raw.value, raw.taint⟩

/-- `ofRaw_bytes` proves conversion retains the exact raw byte list. -/
@[simp] theorem ofRaw_bytes (raw : Unsafe.Construct.Bytes) :
    (ofRaw raw).bytes = raw.value := rfl

/-- `ofRaw_taint` proves conversion retains the exact missing-check account. -/
@[simp] theorem ofRaw_taint (raw : Unsafe.Construct.Bytes) :
    (ofRaw raw).taint = raw.taint := rfl

end Chunk

/-- A raw byte hierarchy whose leaves remain explicitly tainted. -/
inductive Hierarchy where
  | leaf (entry : Grass.Unsafe.Emit.Chunk)
  | group (children : List Hierarchy)
deriving Repr

namespace Hierarchy

/-- Raw byte lists in deterministic left-to-right leaf order. -/
def inputs : Hierarchy → List ByteSeq
  | .leaf entry => [entry.bytes]
  | .group children => children.flatMap inputs

/-- Missing-check accounts in the same leaf order as `Hierarchy.inputs`. -/
def taints : Hierarchy → List Taint
  | .leaf entry => [entry.taint]
  | .group children => children.flatMap taints

end Hierarchy

/-- Caller-owned state transition for one exact raw byte-list input. -/
structure Writer (State Error : Type) where
  write : State → ByteSeq → Except Error State

/-- Successful raw emission state plus the exact inputs and taints presented. -/
structure Receipt (State : Type) where
  state : State
  inputs : List ByteSeq
  taints : List Taint
deriving Repr, DecidableEq

variable {State Error : Type}

/-- Apply one writer call per input, stopping at the first writer error. -/
def run (writer : Writer State Error) : State → List ByteSeq → Except Error State
  | state, [] => .ok state
  | state, bytes :: rest =>
      match writer.write state bytes with
      | .error cause => .error cause
      | .ok next => run writer next rest

/-- `run_nil` makes the empty writer trace explicit. -/
@[simp] theorem run_nil (writer : Writer State Error) (state : State) :
    run writer state [] = .ok state := rfl

/-- `run_cons` exposes the exact next writer input and fail-fast continuation. -/
@[simp] theorem run_cons (writer : Writer State Error) (state : State)
    (bytes : ByteSeq) (rest : List ByteSeq) :
    run writer state (bytes :: rest) =
      match writer.write state bytes with
      | .error cause => .error cause
      | .ok next => run writer next rest := rfl

/-- Stream every raw leaf exactly once in `Hierarchy.inputs` order. -/
def emit (writer : Writer State Error) (initial : State)
    (hierarchy : Hierarchy) : Except Error (Receipt State) :=
  match run writer initial hierarchy.inputs with
  | .error cause => .error cause
  | .ok final =>
      .ok { state := final, inputs := hierarchy.inputs, taints := hierarchy.taints }

/-- `emit_state` exposes the exact ordered writer calls behind successful emission. -/
theorem emit_state {writer : Writer State Error} {initial : State}
    {hierarchy : Hierarchy} {receipt : Receipt State}
    (h : emit writer initial hierarchy = .ok receipt) :
    run writer initial hierarchy.inputs = .ok receipt.state := by
  unfold emit at h
  cases folded : run writer initial hierarchy.inputs with
  | error cause => simp [folded] at h
  | ok final =>
      simp [folded] at h
      cases h
      rfl

/-- `emit_inputs` proves a successful receipt retains the exact callback inputs. -/
theorem emit_inputs {writer : Writer State Error} {initial : State}
    {hierarchy : Hierarchy} {receipt : Receipt State}
    (h : emit writer initial hierarchy = .ok receipt) :
    receipt.inputs = hierarchy.inputs := by
  unfold emit at h
  cases folded : run writer initial hierarchy.inputs with
  | error cause => simp [folded] at h
  | ok final =>
      simp [folded] at h
      cases h
      rfl

/-- `emit_taints` proves a successful receipt retains every raw leaf's taint. -/
theorem emit_taints {writer : Writer State Error} {initial : State}
    {hierarchy : Hierarchy} {receipt : Receipt State}
    (h : emit writer initial hierarchy = .ok receipt) :
    receipt.taints = hierarchy.taints := by
  unfold emit at h
  cases folded : run writer initial hierarchy.inputs with
  | error cause => simp [folded] at h
  | ok final =>
      simp [folded] at h
      cases h
      rfl

end Grass.Unsafe.Emit
