import Grass.Core.Generational
import Grass.Core.Context
import Grass.Platform.Win32.Console
import Grass.Std.Logical.FiniteMap

/-!
# Static console environment

This is a static process-local snapshot for the console boundary.  A later
external applicability claim must connect its fixed routes and handle
generations to an actual process. Its scope excludes concurrent close, reuse,
redirection, changes to the selected output route, and foreign or teardown
output on that route. Resolved live-handle uses require suitable synchronous
handles. The external claim for these restrictions remains owed. This module
installs none of those assumptions, proves no native applicability, and grants
no rights from a `GetStdHandle` result.

The table-copy, sentinel, and unvalidated-handle behavior follows Microsoft's
[GetStdHandle documentation](https://learn.microsoft.com/en-us/windows/console/getstdhandle).
Formal subject/anchor ledger coverage and native applicability remain owed.
-/

namespace Grass.Platform.Win32

open Grass.Core Grass.Std.Logical

/-- Nominal identity for one process snapshot; it is deliberately not a
numeric PID. -/
inductive ProcessTag : Type

/-- A process identity minted in its own nominal domain. -/
abbrev ProcessId := Uid ProcessTag

/-- Nominal identity for an output route. -/
inductive RouteTag : Type

/-- A nominal output-route identity. -/
abbrev RouteId := Uid RouteTag

/-- The concrete handle occurrence includes its non-reusable generation. -/
abbrev GenerationalBV64 := Generational (BitVec 64)

/-- The operation mode carried by a bound console handle. -/
inductive HandleMode where
  | synchronous
  | overlapped
deriving DecidableEq, Repr

/-- Static binding data for one raw Win32 handle value. -/
structure HandleBinding where
  generation : GenerationId
  route : RouteId
  writable : Bool
  mode : HandleMode

namespace HandleBinding

/-- Qualify the supplied raw value with this binding's exact lifetime. -/
def identity (binding : HandleBinding) (raw : BitVec 64) : GenerationalBV64 :=
  ⟨raw, binding.generation⟩

@[simp] theorem identity_value (binding : HandleBinding) (raw : BitVec 64) :
    (binding.identity raw).value = raw := rfl

@[simp] theorem identity_generation (binding : HandleBinding) (raw : BitVec 64) :
    (binding.identity raw).generation = binding.generation := rfl

end HandleBinding

/-- The raw values stored for the three documented standard-handle selectors. -/
structure StandardHandles where
  value : StdHandleId → BitVec 64

/-- One static process-local console environment. -/
structure ConsoleEnvironment where
  process : ProcessId
  caller : ContextId
  provider : ContextId
  standardHandles : StandardHandles
  bindings : FiniteMap (BitVec 64) HandleBinding
  stdoutRoute : RouteId

namespace ConsoleEnvironment

/-- Classify the three documented standard-handle selector values. -/
def standardHandle? (selector : BitVec 32) : Option StdHandleId :=
  if selector = StdHandleId.input.value then some .input
  else if selector = StdHandleId.output.value then some .output
  else if selector = StdHandleId.error.value then some .error
  else none

@[simp] theorem standardHandle?_input : standardHandle? StdHandleId.input.value = some .input := by
  decide

@[simp] theorem standardHandle?_output : standardHandle? StdHandleId.output.value = some .output := by
  decide

@[simp] theorem standardHandle?_error : standardHandle? StdHandleId.error.value = some .error := by
  decide

/-- Look up a usable raw handle after rejecting the two ABI sentinels.
The binding is returned unchanged: writability and route suitability are not
GetStdHandle failure classifications. -/
def routeOf? (environment : ConsoleEnvironment) (raw : BitVec 64) : Option HandleBinding :=
  match UsableHandle.mk? raw with
  | none => none
  | some _ => environment.bindings.lookup raw

theorem routeOf?_lookup {environment : ConsoleEnvironment} {raw : BitVec 64}
    {usable : UsableHandle} (classified : UsableHandle.mk? raw = some usable) :
    environment.routeOf? raw = environment.bindings.lookup raw := by
  unfold routeOf?
  rw [classified]

/-- The fixed raw return relation for GetStdHandle.  A supported selector may
produce its actual table value or the documented invalid sentinel; null and
stale table values remain represented data rather than fabricated failures. -/
def getStdAllowed (environment : ConsoleEnvironment) (selector : BitVec 32)
    (raw : BitVec 64) : Prop :=
  match standardHandle? selector with
  | none => False
  | some handle => raw = environment.standardHandles.value handle ∨
      raw = GetStdHandleResult.invalidHandleValue

instance (environment : ConsoleEnvironment) (selector : BitVec 32) (raw : BitVec 64) :
    Decidable (environment.getStdAllowed selector raw) := by
  unfold getStdAllowed
  split <;> infer_instance

theorem getStdAllowed_output_iff (environment : ConsoleEnvironment) (raw : BitVec 64) :
    environment.getStdAllowed StdHandleId.output.value raw ↔
      raw = environment.standardHandles.value .output ∨
        raw = GetStdHandleResult.invalidHandleValue := by
  simp [getStdAllowed]

theorem getStdAllowed_output_table (environment : ConsoleEnvironment) :
    environment.getStdAllowed StdHandleId.output.value
      (environment.standardHandles.value .output) := by
  exact (environment.getStdAllowed_output_iff _).2 (.inl rfl)

theorem getStdAllowed_output_invalid (environment : ConsoleEnvironment) :
    environment.getStdAllowed StdHandleId.output.value GetStdHandleResult.invalidHandleValue := by
  exact (environment.getStdAllowed_output_iff _).2 (.inr rfl)

end ConsoleEnvironment
end Grass.Platform.Win32
