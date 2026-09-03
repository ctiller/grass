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

`isAtomic` is intent, not ordering: it says what kind of operation this is, while
the ordering it requests is a separate declaration
(`Grass/Memory/Ordering.lean`). An atomic access still declares `reads` and
`writes`, so a compare-and-swap is visibly both.

There is no `isDevice`. There was, reading "performed by, or targets, a device
rather than the CPU", and it was a third source of truth for facts two consulted
mechanisms already carry — conflating them, so neither was recoverable from it.
Who performs an access is `ExecutionContext.kind`, which
`docs/MEMORY_MODEL.md` §7.1 requires every event to carry and which `Grass/Op/Step.lean`
checks against `MachineState.contexts`. What an access targets is its
`AddressSpaceId`, which `denialOf` checks and `AdmittedVocabulary.Admits` requires the
profile to declare; §7.5 makes those spaces non-interchangeable precisely so the
identity carries the fact. The `Bool` was read by nothing, which is how it was
found.
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
The read, write, and execute permissions of a page or section, and whether they
are conveyed for atomic access only.

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
  /--
  The capabilities above are conveyed for **atomic** access only.

  `docs/MEMORY_MODEL.md` §3: "Atomics do not grant ordinary non-atomic access."
  That rule had no mechanism anywhere. There was an `AuthorityState.atomicShared`
  constructor and a theorem about it, and nothing built the constructor, so the
  theorem held of an unreachable case and was deleted — and the reasoning offered
  for the deletion, that the rule had nothing to constrain, was wrong. `Permits` is
  the sole rights gate on the chain `MemoryState.AuthorizedAt` →
  `MemoryState.Granted` → `Grass/Op/Step.lean`'s `refusalOf`,
  and it had no clause about atomicity, (The chain was named as the deleted `Authorizes` function and
`MemoryState.GrantedOfKind` until review checked: the first was deleted, and the
second has no caller under `Grass/` — the provider calls `Granted`, which is
kind-blind on purpose, because `Grass/Op/Step.lean` composes providers conjunctively
and a loan provider refusing an access another authority covers would make that
authority unusable.) so a grant a profile issued authorized an
  atomic and a non-atomic access indistinguishably.

  A `Bool` and not an `OrderingDemand`. §3's rule is that atomic authority does not
  convey ordinary access, which is a fact about what the grant *conveys*; which
  ordering an atomic access must then follow is §7.1 and §7.4's question, it is
  carried by `AccessDescriptor.ordering`, and the profile that answers it is M8's
  `ConsistencyProfile`. Putting an ordering here would be a second place to say what
  the descriptor already says.

  Defaulted, unlike `AllocationRecord.base`, and the difference is real: this field
  *narrows* a permission, so omitting it leaves a declaration meaning exactly what
  the type meant before it existed. A page permission never sets it — no page table
  has such a bit — and it is a grant's field in practice. -/
  atomicOnly : Bool := false
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
  (intent.executes = true → permission.execute = true) ∧
  (permission.atomicOnly = true → intent.isAtomic = true)

instance (permission : Permission) (intent : AccessIntent) :
    Decidable (permission.Permits intent) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
`page.Grants required` holds when a page carrying `page` supplies every capability
`required` demands.

`AccessDescriptor.requiredPermission` is "the page or section permission the access
requires", and nothing compared it to the page. Its only consumer was
`WellFormedIn.permissionSufficient`, which checks it against the descriptor's own
`intent` — so a load could declare it needs read, write and execute on a read-only
page and be admitted, because `denialOf` checked the *intent* and never the
declaration. A field whose only reader is the descriptor that wrote it is a
declaration nothing enforces, which is the shape this layer deleted
`AccessIntent.isDevice` and `AllocationRecord.initialized` for. Review found it one
step short.

Capability by capability, like `Permits`, so a capability added later produces a
type error here rather than defaulting to granted. `atomicOnly` is not compared: it
narrows what a *grant* conveys and a page has no such bit, so a page never demands
it and never supplies it. `permits_of_grants_of_permits` therefore takes the page's
`atomicOnly = false` as a hypothesis rather than assuming it — a page that set the
bit would be outside what this relation describes, and saying so is cheaper than a
clause pretending to handle it.
-/
def Grants (page required : Permission) : Prop :=
  (required.read = true → page.read = true) ∧
  (required.write = true → page.write = true) ∧
  (required.execute = true → page.execute = true)

instance (page required : Permission) : Decidable (page.Grants required) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **A read-only page does not grant a read/write demand.** -/
@[simp] theorem readOnly_not_grants_readWrite : ¬ readOnly.Grants readWrite := by
  simp [Grants, readOnly, readWrite]

/-- It grants a read-only demand, so the theorem above is a restriction rather than
a page that grants nothing. -/
@[simp] theorem readOnly_grants_readOnly : readOnly.Grants readOnly := by
  simp [Grants, readOnly]

/-- **A page granting the demand, and a demand permitting the intent, gives a page
permitting the intent.** The chain `denialOf` relies on, stated so the two clauses
are visibly one rule rather than two overlapping ones. -/
theorem permits_of_grants_of_permits {page required : Permission} {intent : AccessIntent}
    (hatomic : page.atomicOnly = false) (hg : page.Grants required)
    (hp : required.Permits intent) : page.Permits intent :=
  ⟨fun h => hg.1 (hp.1 h), fun h => hg.2.1 (hp.2.1 h), fun h => hg.2.2 (hp.2.2.1 h),
   fun h => by rw [hatomic] at h; exact absurd h (by simp)⟩

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

/-- Read/write conveyed for atomic access only, which is `docs/MEMORY_MODEL.md`
§3's atomic shared access expressed as a right rather than as a state. -/
def atomicReadWrite : Permission :=
  { read := true, write := true, atomicOnly := true }

/-- **Atomic authority does not convey ordinary non-atomic access.**
`docs/MEMORY_MODEL.md` §3, at the gate every access passes. -/
@[simp] theorem atomicReadWrite_not_permits_write :
    ¬ atomicReadWrite.Permits AccessIntent.write := by
  simp [Permits, atomicReadWrite, AccessIntent.write]

/-- Nor an ordinary read: §3 says atomics do not grant ordinary non-atomic
*access*, which is not only writes. -/
@[simp] theorem atomicReadWrite_not_permits_read :
    ¬ atomicReadWrite.Permits AccessIntent.read := by
  simp [Permits, atomicReadWrite, AccessIntent.read]

/-- But it does convey the atomic access it exists for, so the two theorems above
are a restriction rather than a permission that grants nothing. -/
@[simp] theorem atomicReadWrite_permits_atomicReadWrite :
    atomicReadWrite.Permits AccessIntent.atomicReadWrite := by
  simp [Permits, atomicReadWrite, AccessIntent.atomicReadWrite]

/-- And an ordinary permission conveys an atomic access: the restriction runs one
way. A profile that wants atomic-only says so; one that does not has not silently
acquired a new refusal. -/
@[simp] theorem readWrite_permits_atomicWrite :
    readWrite.Permits AccessIntent.atomicWrite := by
  simp [Permits, readWrite, AccessIntent.atomicWrite]

end Permission

end Grass.Memory
