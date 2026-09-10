# Census evidence

This is the pre-removal snapshot supporting
[the approved removal plan](../../HELLO_SPECIALIZATION_REMOVAL.md). It is a
historical audit artifact, not an executable program supplier or a declaration
trust audit. Deletions after the snapshot intentionally make some entries stale.

- `snapshots.json`: six worktrees, exact heads, working status, scanned text-file
  counts. Windows included uncommitted source, including an uncompiled receipt.
- `files.tsv`: 377 distinct paths / 431 content variants. Equal normalized text
  is coalesced across worktrees; each variant records its owning trees.
- `declarations.tsv`: 5,739 lexical declaration headers in that selected surface,
  with line numbers and variant hashes. This is not elaborated declaration count;
  local declarations, comments, macros and multiline headers limit lexical data.
- `text-matches.tsv`: 993 matching lines, including historical documentation and
  authored source. Matches are search leads, not automatically defects.
- `collect.py`: the read-only collection procedure, writing only these audit
  outputs. The worktree paths record the inspection environment and can be
  adjusted for a later census. Do not overwrite this pre-removal evidence to
  imply an old finding has disappeared; make a new dated snapshot instead.

Selection scans tracked and nonignored text files in the six trees, selecting
Hello/Spike1 matches plus complete Assembly, Frontend, Console, console
refinement, Win32, and their immediate test directories. This catches fixed
instruction recipes without a Hello name. Reviewers separately inspected
generic semantics/refinement boundaries, PE modules, ABI/ISA/memory fixtures,
the active Windows dirty files, and ignored frontend experiments. The written
plan records those findings and adjudicates false positives.

This is not a completeness proof over dormant branch history, arbitrary binary
files or every ignored build artifact. Dormant branches and gasm/wsc remain
unreviewed spare parts; imports from them must be inspected before use. The
fixture pipeline's narrow passing tests were not used as proof of compilation
or as evidence that library specialization was absent.

The source snapshots contain no user credentials or external account data.
Hashes describe source content only; they do not grant semantic authority.
