import Lean
import Grass.Std.Logical.Vec
import Grass.Std.Logical.Order

/-!
# Observation-coverage audit

`docs/STDLIB_IMPLEMENTATION_PLAN.md` decision 6 requires that every operation
returning a `Vec` state a law computing the result's `length` **and** a law
computing the result's `get?`, in terms of its arguments'. This tool checks it.

## Why it is a program and not a paragraph

The rule has been rewritten three times. Every version was stated in prose, and
every version was violated in the same commit that stated it — the "at least one
law" rule shipped alongside `truncate` and `clear`, which had none; the
"determination" rule shipped alongside an internal inconsistency about
`splitAt`; and the coverage rule itself shipped alongside `Vec.sum` and
`Vec.count`, which had no laws at all, with `sum` on the right-hand side of
`Vec.length_flatten` where every consumer of that law would meet it.

That is not carelessness three times. It is what an unenforced rule does to a
library changing at this rate, and it was adversarial review rather than the
author that caught each one. `Tools/AxiomAudit.lean` and `Tools/DocstringAudit.py`
exist for the same reason and their module comments say so.

## What it checks, and what it deliberately does not

A declaration is an **operation** if it is a `def` in `Grass.Std.Logical.Vec`
whose result type is a `Vec`. For each, the audit looks for a theorem somewhere
in the environment whose statement applies `Vec.length` to a term headed by that
operation, and likewise for `Vec.get?`.

Three deliberate limits, stated because a checker that overstates its reach is
worse than none:

- It does not check that a law is *correct*, only that it exists and is about the
  right thing. The kernel checks correctness.
- It does not reach operations returning `Bool`, `Nat`, `Option`, or `Prop` —
  roughly half the module. Decision 6's clause (i) is phrased over `length` and
  `get?` of a result, which presupposes the result is a `Vec`. Those operations
  are counted and listed as outside the bar rather than silently passed, so the
  number is visible.
- It does not implement clause (ii), the `empty`/`push` recursion, nor the alias
  clause. Operations that pass on those are named in `recursionOrAlias` below and
  the exemption is explicit, which is the point: an exemption in a list is
  reviewable, an exemption in prose is not.
-/

open Lean

namespace Grass.Tools

/-- The observations decision 6 is phrased over. -/
def lengthName : Name := `Grass.Std.Logical.Vec.length

/-- The checked accessor. -/
def getName : Name := `Grass.Std.Logical.Vec.get?

/--
Operations that satisfy decision 6 by its clause (ii) or its alias clause rather
than by a `length`/`get?` pair, with the reason.

Listed rather than inferred, so that adding one is a reviewable edit. Adversarial
review found that the alias clause as originally worded admitted a cycle — two
operations each citing the other and neither carrying a law — so an alias
exemption is only as good as the fact that a human wrote it down here.
-/
def recursionOrAlias : List (Name × String) :=
  [ (`Grass.Std.Logical.Vec.foldl, "clause (ii): foldl_empty, foldl_push"),
    (`Grass.Std.Logical.Vec.foldr, "clause (ii): foldr_empty, foldr_push"),
    (`Grass.Std.Logical.Vec.flatten, "clause (ii): flatten_empty, flatten_push"),
    (`Grass.Std.Logical.Vec.pop?, "clause (ii): pop?_empty, pop?_push"),
    (`Grass.Std.Logical.Vec.truncate, "alias: truncate_eq_take, and take passes (i)"),
    (`Grass.Std.Logical.Vec.clear, "alias: clear_eq_empty, and empty passes (i)"),
    (`Grass.Std.Logical.Vec.splitAt, "alias: splitAt_eq, and take/drop pass (i)"),
    (`Grass.Std.Logical.Vec.fromList, "the constructor; toList_fromList characterises it"),
    (`Grass.Std.Logical.Vec.append,
      "laws stated over the `++` notation: length_append, get?_append_left, get?_append_right") ]

/-!
The `append` entry is the first thing this audit found, and it is worth recording
what kind of finding it is. `Vec.length_append` and the two `get?_append_*` laws
exist, but every one is stated over `v ++ w`, which elaborates through the
`Append` instance rather than as an application of `Vec.append`. So the laws
cover the operation *as consumers write it* and leave the bare name uncovered.

That is a naming observation rather than a missing law, which is why it is an
exemption with a reason instead of a weakening of the check. The alternative —
teaching the audit to see through instance applications — would make it accept a
class of genuine gaps in exchange for tidying one false one.
-/

/-- Whether `e` contains `obs` applied to a term headed by `op`. -/
partial def observes (obs op : Name) (e : Expr) : Bool :=
  let here :=
    e.getAppFn.constName? == some obs &&
      e.getAppArgs.any fun arg => arg.getAppFn.constName? == some op
  here || match e with
    | .app f a => observes obs op f || observes obs op a
    | .lam _ t b _ => observes obs op t || observes obs op b
    | .forallE _ t b _ => observes obs op t || observes obs op b
    | .letE _ t v b _ => observes obs op t || observes obs op v || observes obs op b
    | .mdata _ b => observes obs op b
    | .proj _ _ b => observes obs op b
    | _ => false

/-- Whether a constant's result type is a `Vec`. -/
partial def returnsVec (e : Expr) : Bool :=
  match e with
  | .forallE _ _ b _ => returnsVec b
  | _ => e.getAppFn.constName? == some `Grass.Std.Logical.Vec

end Grass.Tools

open Grass.Tools in
run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  let vecNs := `Grass.Std.Logical.Vec
  let exempt := recursionOrAlias.map Prod.fst

  -- Every def in the Vec namespace, split by whether the bar reaches it.
  let mut ops : Array Name := #[]
  let mut outsideBar : Array Name := #[]
  for (name, info) in env.constants.toList do
    unless vecNs.isPrefixOf name && !name.isInternal do continue
    match info with
    | .defnInfo d =>
      if returnsVec d.type then ops := ops.push name else outsideBar := outsideBar.push name
    | _ => pure ()

  -- Collect every theorem statement once.
  let mut theorems : Array Expr := #[]
  for (_, info) in env.constants.toList do
    match info with
    | .thmInfo t => theorems := theorems.push t.type
    | _ => pure ()

  let mut missing : Array (Name × String) := #[]
  let mut checked : Nat := 0
  for op in ops do
    if exempt.contains op then continue
    checked := checked + 1
    let hasLength := theorems.any fun t => observes lengthName op t
    let hasGet := theorems.any fun t => observes getName op t
    if !hasLength && !hasGet then
      missing := missing.push (op, "no length law and no get? law")
    else if !hasLength then
      missing := missing.push (op, "no law computing its length")
    else if !hasGet then
      missing := missing.push (op, "no law computing its get?")

  if missing.isEmpty then
    logInfo m!"observation-coverage audit: {checked} Vec-returning operations each carry a \
length law and a get? law; {exempt.length} exempt by clause (ii) or the alias clause; \
{outsideBar.size} declarations outside the bar's reach"
  else
    let lines := missing.map fun (n, why) => m!"  {n}: {why}"
    throwError m!"observation-coverage audit failed; \
docs/STDLIB_IMPLEMENTATION_PLAN.md decision 6 requires a length law and a get? law \
for every Vec-returning operation:\n{MessageData.joinSep lines.toList "\n"}"
