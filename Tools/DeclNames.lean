import Lean

/-!
# Every declaration name the build knows

`Tools/DocstringAudit.py` requires a strong claim in a docstring to name the type
or theorem that enforces it. It checked that the sentence contained *a backticked
identifier* and nothing more, so an invented name satisfied it — a reviewer
passed the audit with a sentence naming
`encodeMem_is_canonical_and_injective_over_all_addresses`, which does not exist
and never did. That is the exact defect the tool's own header says it was built
for: `.github/workflows/library.yml` records "one naming a theorem that did not
exist".

The tool cannot be given a Lean environment, so this prints one for it. Every
constant name in the environment, one per line, with `private` mangling stripped
so a docstring can name a private theorem by the name it is written under.

Not restricted to `Grass`: docstrings legitimately name core declarations —
`BitVec`, `List.find?`, `Option.isSome` — and a checker that rejected those would
push authors towards naming nothing rather than towards naming something real.

This is not a proof and not an audit. It is a fact dump, and the tool that reads
it still cannot tell whether the named theorem proves the sentence. It closes one
gap: whether the name resolves at all.
-/

open Lean

partial def modulesOnDisk (root : System.FilePath) (prefix_ : Name) :
    IO (Array Name) := do
  let mut found : Array Name := #[]
  for entry in (← root.readDir) do
    let name := entry.fileName
    if ← entry.path.isDir then
      found := found ++ (← modulesOnDisk entry.path (prefix_ ++ Name.mkSimple name))
    else if name.endsWith ".lean" then
      let stem := name.dropEnd 5 |>.toString
      found := found.push (prefix_ ++ Name.mkSimple stem)
  return found

def main : IO Unit := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let lakeLib := System.FilePath.mk ".lake" / "build" / "lib" / "lean"
  Lean.searchPathRef.modify fun sp => lakeLib :: sp

  let onDisk ← modulesOnDisk (System.FilePath.mk "Grass") `Grass
  if onDisk.isEmpty then
    throw <| IO.userError "declaration list coverage gap: no modules found under Grass/"
  let imports := onDisk.map fun m => ({ module := m } : Import)
  let env ← importModules imports {}

  for (name, _) in env.constants.toList do
    let user := (privateToUserName? name).getD name
    unless user.isInternal do
      IO.println user.toString
