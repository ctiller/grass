import Tests.ISA.X86.NasmCorpus
import Tests.ISA.X86.RipCorpus
import Tests.ISA.X86.DecodeCorpus
import Tests.ISA.X86.MachineProbes
import Tests.ISA.X86.SourceCorpus
import Tests.ABI.Win64.UnwindCorpus

/-!
# The one entry point for every corpus

`lake env lean --run` looks for a root `main`, so each corpus module used to
declare one. Six root `main`s cannot coexist in a single environment, and
`audit-trust.ps1` builds exactly that: it imports the whole selected test
closure at once, and failed before auditing anything with `main` already loaded
from another module. `g-construct:58` reported it blocking their gate.

Splitting the emitters into a separate library would have hidden the same
collision behind a build-configuration change. One `main` that dispatches by
name is smaller, keeps every corpus inside the audited closure, and makes the
set of emitters something a reader can enumerate here rather than discover by
grepping for `main`.

This module is also the guard against the collision returning. It imports every
corpus *and* declares `main`, so a corpus that declares a root `main` again
fails the build here immediately rather than surfacing later as an audit that
cannot load its own closure.

Usage: `lake env lean --run Tests/Emit.lean <corpus>`.
-/

/-- The corpora this can emit, and what each writes. -/
def emitters : List (String × IO Unit) :=
  [ ("nasm", emitNasmCorpus)
  , ("rip", emitRipCorpus)
  , ("decode", emitDecodeCorpus)
  , ("probes", emitMachineProbes)
  , ("sources", emitSourceCorpus)
  , ("unwind", emitUnwindCorpus) ]

/-- Emit the named corpus on standard output.

An unknown or missing name is an error rather than a silent no-op: a
differential whose corpus file came back empty would otherwise report agreement
on nothing, which is the failure mode the coverage floors in `Tools/` exist to
prevent. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [name] =>
    match emitters.find? (fun p => p.1 = name) with
    | some (_, emit) => emit; return 0
    | none =>
      IO.eprintln s!"unknown corpus {name}; expected one of \
        {String.intercalate ", " (emitters.map Prod.fst)}"
      return 1
  | _ =>
    IO.eprintln s!"usage: lake env lean --run Tests/Emit.lean <corpus>, where \
      <corpus> is one of {String.intercalate ", " (emitters.map Prod.fst)}"
    return 1
