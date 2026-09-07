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
      found := found.push (prefix_ ++ Name.mkSimple (name.dropEnd 5 |>.toString))
  return found

run_cmd do
  let onDisk ← modulesOnDisk (System.FilePath.mk "Grass") `Grass
  let imports := onDisk.map fun moduleName => ({ module := moduleName } : Import)
  unsafe Lean.enableInitializersExecution
  let env ← importModules imports {} 0 #[] false true
  -- The same coverage guard `Tools/AxiomAudit.lean` carries, for the same
  -- reason: a module missing from the imported environment would silently shrink the name set,
  -- and every docstring naming one of its declarations would be reported as
  -- naming nothing. A loud failure beats a mystery finding.
  let imported := env.header.moduleNames
  let missing := onDisk.filter fun m => !imported.contains m
  unless missing.isEmpty do
    throwError m!"declaration list coverage gap: these modules exist under Grass/ but are not imported by Tools/DeclNames.lean:
{MessageData.joinSep (missing.toList.map (m!"  {·}")) "
"}"
  let mut out : Array String := #[]
  for (name, _) in env.constants.toList do
    let user := (privateToUserName? name).getD name
    unless user.isInternal do
      out := out.push user.toString
  for line in out do
    IO.println line
