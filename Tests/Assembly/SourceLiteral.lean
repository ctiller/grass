import Lean

/-!
Embed authored characters as a literal list. This performs the same file read
as `include_str`; it creates data, not a proof or an evaluator-backed axiom.
Direct fixture elaboration remains required when the authored file changes.
The character-list representation avoids kernel UTF-8 decoding of a large
String literal before the source parser can run.
-/

open Lean Elab Term

elab "source_chars " source:str : term =>
  return toExpr source.getString.toList

elab "include_source_chars " path:str : term => do
  let context ← readThe Lean.Core.Context
  let sourcePath := System.FilePath.mk context.fileName
  let some directory := sourcePath.parent
    | throwError "cannot compute the source directory for {sourcePath}"
  let source ← IO.FS.readFile (directory / path.getString)
  return toExpr source.toList
