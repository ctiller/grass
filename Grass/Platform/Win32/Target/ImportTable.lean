import Grass.Target.Raw

/-!
# Win32 import-table knowledge

Which uniquely resolved import slot and loaded target mean which Win32 API.
Both the named slot occurrence and its nonzero resolved address are supplied
by the artifact loader/provider. A different program may use any import order
or subset of this API surface.
-/

namespace Grass.Platform.Win32.Target

/-- The Win32 API surface this platform profile realizes. Every constructor
is one `KERNEL32.dll` export this platform's `decode`/`encodeReturn`
(`Grass/Platform/Win32/Target/Decode.lean`,
`Grass/Platform/Win32/Target/Return.lean`) know how to interpret. An import
this profile does not recognize is not a constructor here at all, so
`resolvedApiOf` answers `none` for it, which leaves the machine stuck — correct,
since an unrealized platform call is a program bug or a profile gap, never
silent progress (`Grass.Target.Machine.stuck_of_undecoded`). -/
inductive Api where
  | getStdHandle
  | writeFile
  | readFile
  | exitProcess
  | getProcessHeap
  | heapAlloc
  | heapReAlloc
  | heapFree
  | queryPerformanceCounter
deriving DecidableEq, Repr

/-- Every export this profile realizes lives in `KERNEL32.dll`. -/
def Api.library : Api → String := fun _ => "KERNEL32.dll"

/-- The exported symbol name, exactly as it appears in a PE import
directory / import library. -/
def Api.symbol : Api → String
  | .getStdHandle => "GetStdHandle"
  | .writeFile => "WriteFile"
  | .readFile => "ReadFile"
  | .exitProcess => "ExitProcess"
  | .getProcessHeap => "GetProcessHeap"
  | .heapAlloc => "HeapAlloc"
  | .heapReAlloc => "HeapReAlloc"
  | .heapFree => "HeapFree"
  | .queryPerformanceCounter => "QueryPerformanceCounter"

/-- Every API this profile knows, for lookup by name. -/
def Api.all : List Api :=
  [.getStdHandle, .writeFile, .readFile, .exitProcess, .getProcessHeap,
    .heapAlloc, .heapReAlloc, .heapFree, .queryPerformanceCounter]

/-- One loader-supplied resolution of a named import slot. The symbol retains
the program's import-table identity; `targetAddress` is the loader/provider's
resolved address for that occurrence. -/
structure ResolvedImport where
  /-- Exact named slot occurrence supplied by the artifact loader. -/
  importSymbol : Grass.Target.ImportSymbol
  /-- Address supplied for that occurrence by the loader/provider.
  `resolvedApiOf` rejects zero rather than this field enforcing nonzeroness. -/
  targetAddress : UInt64
deriving DecidableEq, Repr

/-- Resolve a loaded call target through one exact, unique import-slot binding.

The supplied bindings are loader/provider identity inputs. This lookup checks
their internal agreement with the observed target; it does not establish OS
provider correspondence or that loaded memory remained immutable. -/
def resolvedApiOf (bindings : List ResolvedImport) (slotAddress : Nat)
    (loadedTarget : UInt64) : Option Api :=
  match bindings.filter (fun binding => binding.importSymbol.slotAddress == slotAddress) with
  | [binding] =>
      if binding.targetAddress == 0 then none
      else if binding.targetAddress == loadedTarget then
        Api.all.find? (fun api =>
          api.library == binding.importSymbol.library &&
          api.symbol == binding.importSymbol.symbol)
      else none
  | _ => none

/-- `resolvedApiOf_binding` proves every successful lookup comes from the unique binding at the requested
slot and retains its exact nonzero loaded target. -/
theorem resolvedApiOf_binding {bindings : List ResolvedImport} {slotAddress : Nat}
    {loadedTarget : UInt64} {api : Api}
    (found : resolvedApiOf bindings slotAddress loadedTarget = some api) :
    ∃ binding,
      bindings.filter (fun candidate => candidate.importSymbol.slotAddress == slotAddress) =
        [binding] ∧
      binding.targetAddress = loadedTarget ∧ binding.targetAddress ≠ 0 := by
  unfold resolvedApiOf at found
  split at found <;> try contradiction
  next filtered binding slotExact =>
    split at found <;> try contradiction
    next nonzero =>
      split at found <;> try contradiction
      next targetExact =>
        refine ⟨binding, slotExact, ?_, ?_⟩
        · simpa using targetExact
        · simpa using nonzero

end Grass.Platform.Win32.Target
