/-!
# Access intent and permissions

`docs/MEMORY_MODEL.md` §4 requires read, write, and execute permissions to be
distinct, and §1 requires every access to declare its intent and the page or
section permissions it needs.

Intent is a set of capabilities rather than a single tag because a
read-modify-write reads and writes in one access, and collapsing that to "write"
would lose the read the consistency model has to account for. `Permits` is the
enforcement predicate: it is stated as an implication per capability, so adding a
capability later cannot silently widen what an existing permission allows.
-/

namespace Grass.Memory

/--
What an access does to the bytes it names.

`isAtomic` and `isDevice` are intent, not ordering: they say what kind of
operation this is, while the ordering it requests is a separate declaration
(`Grass/Memory/Ordering.lean`). An atomic access still declares `reads` and
`writes`, so a compare-and-swap is visibly both.
-/
structure AccessIntent where
  /-- The access observes the bytes it names. -/
  reads : Bool := false
  /-- The access modifies the bytes it names. -/
  writes : Bool := false
  /-- The access fetches the bytes it names as instructions. -/
  executes : Bool := false
  /-- The access is atomic with respect to its declared scope. -/
  isAtomic : Bool := false
  /-- The access is performed by, or targets, a device rather than the CPU. -/
  isDevice : Bool := false
deriving DecidableEq, Repr

namespace AccessIntent

/-- An ordinary load. -/
def read : AccessIntent := { reads := true }

/-- An ordinary store. -/
def write : AccessIntent := { writes := true }

/-- A non-atomic read-modify-write, such as `add [mem], reg`. -/
def readWrite : AccessIntent := { reads := true, writes := true }

/--
An instruction fetch.

`reads` as well as `executes`: a fetch really does observe the bytes, and the
consistency model has to account for that observation like any other. What
`executes` adds is the permission demand, which `Permission.Permits` checks
separately. An intent that executed without reading would describe an operation
that consumed instructions it never looked at.
-/
def execute : AccessIntent := { reads := true, executes := true }

/-- An atomic read-modify-write, such as a `lock`-prefixed operation. -/
def atomicReadWrite : AccessIntent := { reads := true, writes := true, isAtomic := true }

/-- An atomic load. -/
def atomicRead : AccessIntent := { reads := true, isAtomic := true }

/-- An atomic store. -/
def atomicWrite : AccessIntent := { writes := true, isAtomic := true }

/--
An access that touches no bytes is not an access; profiles must reject it rather
than treat it as a harmless no-op (`docs/FOUNDATION.md` law 8).

Inertness is about `reads` and `writes` only. `executes` is a permission demand
rather than a way of touching bytes — see `execute` above, which reads — so an
intent that set `executes` alone would still be inert, and is rejected. That is
the strict direction: it describes an operation that consumed instructions it
never observed.
-/
def IsInert (intent : AccessIntent) : Prop :=
  intent.reads = false ∧ intent.writes = false

instance (intent : AccessIntent) : Decidable intent.IsInert :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem not_isInert_read : ¬ read.IsInert := by simp [IsInert, read]

@[simp] theorem not_isInert_write : ¬ write.IsInert := by simp [IsInert, write]

end AccessIntent

/--
The read, write, and execute permissions of a page or section.

Kept distinct per `docs/MEMORY_MODEL.md` §4. Image sections use least privilege,
and stack storage carries explicit execute state rather than inheriting one.
-/
structure Permission where
  /-- Reads are permitted. -/
  read : Bool := false
  /-- Writes are permitted. -/
  write : Bool := false
  /-- Instruction fetch is permitted. -/
  execute : Bool := false
deriving DecidableEq, Repr

namespace Permission

/-- No access at all, such as a guard page. -/
def none : Permission := {}

/-- Read-only data. -/
def readOnly : Permission := { read := true }

/-- Ordinary read/write data, including stack storage. -/
def readWrite : Permission := { read := true, write := true }

/-- Executable code, without write permission. -/
def readExecute : Permission := { read := true, execute := true }

/--
`permission.Permits intent` holds when `permission` allows everything `intent`
does.

Stated capability by capability rather than as a subset of a packed
representation, so that a later capability added to `AccessIntent` produces a
type error here instead of silently defaulting to permitted.
-/
def Permits (permission : Permission) (intent : AccessIntent) : Prop :=
  (intent.reads = true → permission.read = true) ∧
  (intent.writes = true → permission.write = true) ∧
  (intent.executes = true → permission.execute = true)

instance (permission : Permission) (intent : AccessIntent) :
    Decidable (permission.Permits intent) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

@[simp] theorem none_not_permits_read : ¬ none.Permits .read := by
  simp [Permits, none, AccessIntent.read]

@[simp] theorem readOnly_not_permits_write : ¬ readOnly.Permits .write := by
  simp [Permits, readOnly, AccessIntent.write]

@[simp] theorem readOnly_permits_read : readOnly.Permits .read := by
  simp [Permits, readOnly, AccessIntent.read]

/-- Writing to a read-execute section is denied. This is the fact an image
section's least-privilege claim rests on. -/
@[simp] theorem readExecute_not_permits_write : ¬ readExecute.Permits .write := by
  simp [Permits, readExecute, AccessIntent.write]

/-- Executing read/write data is denied. -/
@[simp] theorem readWrite_not_permits_execute : ¬ readWrite.Permits .execute := by
  simp [Permits, readWrite, AccessIntent.execute]

end Permission

end Grass.Memory
