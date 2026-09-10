import Grass.Target.Raw

/-!
# Win32 import-table knowledge

Which `KERNEL32.dll` import slot means which Win32 API, recovered from the
loaded program's own `Sectioned.imports` (`Grass/Target/Raw.lean`). Nothing
here resolves an address to a slot — that is the artifact loader's job, fixed
by the PE import directory before this platform ever runs. This module only
says what a *named* slot means, so it is parameterized by the program's own
import list rather than assuming any fixed layout: a different program with
a different import order, or one that imports only a subset of this API
surface, still decodes correctly as long as its `ImportSymbol.symbol`
strings match a name below.
-/

namespace Grass.Platform.Win32.Target

/-- The Win32 API surface this platform profile realizes. Every constructor
is one `KERNEL32.dll` export this platform's `decode`/`encodeReturn`
(`Grass/Platform/Win32/Target/Decode.lean`,
`Grass/Platform/Win32/Target/Return.lean`) know how to interpret. An import
this profile does not recognize is not a constructor here at all, so
`apiOf` answers `none` for it, which leaves the machine stuck — correct,
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

/-- Which API, if any, a call through `slotAddress` reaches, given the
program's own import table.

`none` when no import occupies the slot, or the occupying import's
`(library, symbol)` is not one this profile realizes. The *first* import
found at the slot is used; `Sectioned.WellFormed` does not itself guarantee a
unique occupant per slot, and a table with two conflicting entries at one
address is a loader well-formedness failure this platform does not
adjudicate — it is not this seam's job to detect a malformed import table,
only to decode a call through a slot the way one named entry says to. -/
def apiOf (imports : List Grass.Target.ImportSymbol) (slotAddress : Nat) : Option Api :=
  match imports.find? (fun entry => entry.slotAddress == slotAddress) with
  | none => none
  | some entry =>
      Api.all.find? (fun api => api.library == entry.library && api.symbol == entry.symbol)

end Grass.Platform.Win32.Target
