import Grass.ISA.Wasm.Target.Instr
import Grass.ISA.Wasm.Types

/-!
# The Wasm module (`Raw`), native-call shapes, and faults

`Value` is reused from `Grass.ISA.Wasm.Types` rather than redeclared. This
file supplies everything else the ISA seam needs before `State`/`step`:

- `Module`, the assembled program (`Grass.Target.ISA.Raw`) an artifact writer
  serializes and a loader installs. It extends the pre-existing
  `Grass.ISA.Wasm.Module` family (types, imports, function bodies as `List
  Instr`, memory, globals, exports, data segments, an optional start
  function) rather than the smaller local-checked-invocation `Module` in
  `Grass/ISA/Wasm/Module.lean`, which models a different, narrower family
  (no memory, no control flow) for a different consumer
  (`Grass/ISA/Wasm/{LocalStep,Invocation}.lean`) and is left untouched.
- `NativeCall`/`NativeReturn`, the ISA-level view of a call to an imported
  function and of the platform's answer, per `Grass.Target.ISA`: the ISA
  supplies the register/stack/memory view, the platform decodes it into a
  `Service` request and encodes the response back.
- `Fault`, why a step can get stuck.
- `InitialContext`, what a platform (WASI, or any host) must supply to start
  a module: which function to run, and what the linear memory holds at
  entry (beyond the module's own data segments) — argv/envp/stdio are
  host-side per `docs/TARGET_SEAMS.md`, so they are not named here.
-/
namespace Grass.ISA.Wasm.Target

open Grass.ISA.Wasm (Value ValType FuncType)

/-- A module-level global: its type, whether it is importable/settable after
init, and its initializer. No global initializer expressions (`global.get`
of an imported global, etc.): the initial value is a constant, which is all
the MVP integer family's producers need. -/
structure Global where
  type : ValType
  mutable : Bool
  init : Value
deriving Repr, DecidableEq

/-- One imported function. The MVP family only imports functions (no
imported memories/globals/tables): a hosted program's other needs go through
`Service.Domain` requests once imported, not through further Wasm imports. -/
structure Import where
  moduleName : String
  fieldName : String
  typeIndex : Nat
deriving Repr, DecidableEq

/-- One defined (non-imported) function. -/
structure Function where
  typeIndex : Nat
  locals : List ValType
  body : List Instr
deriving Repr, DecidableEq

/-- A function export. Memory/global exports are not modeled: nothing in
this MVP family's `State` needs to resolve one (a platform that needs a
module's memory reaches it through `NativeCall.read`, not through Wasm
export resolution). -/
structure Export where
  name : String
  funcIndex : Nat
deriving Repr, DecidableEq

/-- A data segment: `bytes` are installed into linear memory at `offset` by
`initial`. No data-segment initializer expressions (`global.get`-relative
offsets): `offset` is already the constant it would evaluate to, which is
all a producer emitting this family needs to express. -/
structure Data where
  offset : Nat
  bytes : List UInt8
deriving Repr, DecidableEq

/-- The assembled Wasm module: `Grass.Target.ISA.Raw` for this target. -/
structure Module where
  types : List FuncType
  imports : List Import
  functions : List Function
  /-- Linear memory size at instantiation, in 64 KiB pages. -/
  memoryMinPages : Nat
  globals : List Global
  exports : List Export
  data : List Data
  start : Option Nat
deriving Repr, DecidableEq

/-- Wasm numbers imported and defined functions in one space, imports
first. `funcTypeOf` resolves either kind to its signature through the type
section, which is what every call site (`call`, a native return, `initial`)
needs and none of them should recompute by hand. -/
def Module.funcTypeOf (m : Module) (index : Nat) : Option FuncType :=
  if index < m.imports.length then
    (m.imports[index]?).bind (fun imp => m.types[imp.typeIndex]?)
  else
    (m.functions[index - m.imports.length]?).bind (fun f => m.types[f.typeIndex]?)

/-- The body of a *defined* function (`none` for an import or an
out-of-range index). -/
def Module.functionBody (m : Module) (index : Nat) : Option Function :=
  if index < m.imports.length then none
  else m.functions[index - m.imports.length]?

/-- Linear memory size in bytes at instantiation. -/
def Module.memoryBytes (m : Module) : Nat := m.memoryMinPages * 65536

/-- The function index a module exports under `name`, if any. Export names
are unique in a well-formed module, so the first match is the only one. -/
def Module.exportedFunc (m : Module) (name : String) : Option Nat :=
  (m.exports.find? (fun e => e.name == name)).map Export.funcIndex

/-- One past the last index of the function index space. `functionBody` is
`none` here, so a frame entered at this index faults on its first `step`:
this is the index `initial` uses for an entry export the module does not
resolve, which is why an unresolvable entry name is a visible refusal rather
than a silent run of function `0`. -/
def Module.unresolvedIndex (m : Module) : Nat := m.imports.length + m.functions.length

/-- What a platform hands the machine at entry, per `Grass.Target.ISA`: the
*export name* of the function to run, and any memory contents beyond the
module's own data segments (a WASI platform lays out argv/envp/environ bytes
here before the module's declared data segments are installed by `initial`,
exactly as an ELF/PE loader lays out the initial stack for a native ISA).

The entry is a name, not an index, because `Grass.Target.Platform.entry :
Environment → isa.InitialContext` is not handed the module: only `initial`
sees both, so only `initial` can resolve the name through
`Module.exportedFunc`. A platform that named an index would be guessing. -/
structure InitialContext where
  startExport : String
  initialMemory : List (Nat × List UInt8)
deriving Repr, DecidableEq

/-- The ISA-level view of a call to an imported function, handed to the
platform to decode into a `Service.Domain` request. `read` gives the
platform read access to linear memory (e.g. to pull a string argument out of
memory by address and length) without exposing the whole memory function or
letting the platform mutate it directly. -/
structure NativeCall where
  importIndex : Nat
  moduleName : String
  fieldName : String
  args : List Value
  read : Nat → Nat → Option (List UInt8)

/-- The machine-level effect of the platform's answer: result values to push
on the caller's stack, and any memory writes (e.g. a `read()` call writing
bytes back into a caller-supplied buffer). -/
structure NativeReturn where
  results : List Value
  writes : List (Nat × List UInt8)

/-- Why a step got stuck. Every reason names an architectural fact about the
*machine*, never a program: `outOfBounds` covers every load, store, and data
segment install past the linear memory's length; `undecodable` covers a call
through an index the module does not resolve (including `call_indirect`,
which this MVP family accepts syntactically — §`decode`/`encode` — but has
no table section to resolve, so it always faults this way; a future
extension adding tables would give it a real semantics without touching this
type). -/
inductive Fault where
  | unreachable
  | outOfBounds
  | divideByZero
  | integerOverflow
  | stackExhausted
  | typeMismatch
  | undecodable
deriving DecidableEq, Repr

end Grass.ISA.Wasm.Target
