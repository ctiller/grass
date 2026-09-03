import Grass.Memory.Loan
import Grass.Op.Step

/-!
# The seam fixture: two independent operation families

This file is the acceptance criterion for M1's facet seam. It lives outside
`Grass/Memory/`, defines two operation families that know nothing about each
other, and drives them through the generic transition relation.

Nine things it has to demonstrate, and does:

1. a new operation type introduced without editing a master sum or a registry;
2. that type packaged existentially as `SomeOperation`;
3. read, write, read-modify-write, allocate, release, and atomic facets declared;
4. fault and obligation facets declared;
5. the generic transition consuming those facets;
6. invalid provenance, ranges, and ledger effects rejected;
7. alias conflicts detected across *distinct* allocations naming the same bytes;
8. partial effects preserved when a compound operation faults;
9. a second, independently defined family coexisting with the first.

If any of these could not be written cleanly, the seam would not be real. The two
families below share no type, no registry entry, and no import of each other —
only `Grass.Op.Facets`.
-/

namespace Grass.Tests.FakeIsa

open Grass.Core Grass.Memory Grass.Obligation Grass.Op Grass.Std.Logical

/-! ## Shared setting -/

private def allocs₀ : FreshSupply AllocTag := .initial
private def allocs₁ := allocs₀.fresh.2
private def allocs₂ := allocs₁.fresh.2

/-- A data buffer. -/
def bufferAlloc : AllocId := allocs₀.fresh.1

/-- A second allocation that maps the *same bytes* as `bufferAlloc` — a
host-visible view of a device buffer, say. Distinct identity, same storage. -/
def viewAlloc : AllocId := allocs₁.fresh.1

/-- A read-only allocation. -/
def constAlloc : AllocId := allocs₂.fresh.1

/-- A stack reservation, used by the frame authority provider. -/
def stackAlloc : AllocId := allocs₂.fresh.2.fresh.1

/-- Storage reachable only through a borrow, used by the loan authority
provider. Separate from `bufferAlloc` so that guarding it does not put every
ordinary buffer access behind a loan — a loan provider guards what is borrowed,
not everything the program can name. -/
def borrowedAlloc : AllocId := allocs₂.fresh.2.fresh.2.fresh.1

private def epochs₀ : FreshSupply EpochTag := .initial
/-- The first epoch. -/
def epoch₀ : EpochId := epochs₀.fresh.1

private def contexts₀ : FreshSupply ContextTag := .initial
/-- The program thread. -/
def thread₀ : ContextId := contexts₀.fresh.1

/-- The device engine. A genuinely distinct execution context, which is what
makes its access to shared bytes a conflict rather than ordinary program order. -/
def engine₀ : ContextId := contexts₀.fresh.2.fresh.1

/-- A third context, which neither holds nor lends anything, so a fixture can ask
what a stranger may do. -/
def engine₁ : ContextId := contexts₀.fresh.2.fresh.2.fresh.1

private def obligations₀ : FreshSupply ObligationTag := .initial
/-- The obligation an allocation creates. -/
def releaseObligationId : ObligationId := obligations₀.fresh.1

/-- An obligation identity that is never live. -/
def ghostObligationId : ObligationId := obligations₀.fresh.2.fresh.1

/-- A second identity that is never live. -/
def ghostObligationId₂ : ObligationId := obligations₀.fresh.2.fresh.2.fresh.1

/-- An identity a fabricating delta would install. -/
def fabricatedObligationId : ObligationId :=
  obligations₀.fresh.2.fresh.2.fresh.2.fresh.1

/-- An identity that is fresh before the effect runs, which two creates in one
effect both target. -/
def collidingObligationId : ObligationId :=
  obligations₀.fresh.2.fresh.2.fresh.2.fresh.2.fresh.1

/-- Provenance of the buffer. -/
def bufferProv : Provenance :=
  { space := .cpuVirtual, root := bufferAlloc, epoch := epoch₀, source := .virtualAlloc
    rootExtent := ⟨0, 64⟩, path := [] }

/-- Provenance of the aliasing view. Different allocation identity, same bytes. -/
def viewProv : Provenance := { bufferProv with root := viewAlloc, source := .mappedFile }

/-- Provenance of the read-only allocation. -/
def constProv : Provenance := { bufferProv with root := constAlloc, source := .imageMapping }

/-- Provenance of the stack reservation. -/
def frameProv : Provenance := { bufferProv with root := stackAlloc, source := .stack }

/-- A third allocation, aliased to `viewAlloc` rather than to `bufferAlloc`, so
reaching it from the buffer takes two declared hops. -/
def chainedAlloc : AllocId := allocs₂.fresh.2.fresh.2.fresh.2.fresh.1

/-- Provenance of the far end of the alias chain. -/
def chainedProv : Provenance := { bufferProv with root := chainedAlloc, source := .mappedFile }

/-- A host-visible *device* view of the buffer's storage. `docs/MEMORY_MODEL.md` §7.5
names exactly this pair -- a host-visible device buffer and the allocation behind it --
among the storage that is shared without being the same allocation. -/
def deviceViewAlloc : AllocId := allocs₂.fresh.2.fresh.2.fresh.2.fresh.2.fresh.1

/-- Its provenance: a different address space and a different allocator from the
buffer's, over storage the state declares shared. -/
def deviceProv : Provenance :=
  { bufferProv with
    root := deviceViewAlloc, space := .deviceHostVisible, source := .deviceMemory }

/-- Provenance of the borrowed storage. -/
def borrowedProv : Provenance := { bufferProv with root := borrowedAlloc }

/-- Provenance naming the buffer in an epoch it has moved past. Structurally
impeccable; the state is what refuses it. -/
def staleProv : Provenance := { bufferProv with epoch := epochs₀.fresh.2.fresh.1 }

/-- A descriptor builder, so the families below read as declarations. -/
def acc (prov : Provenance) (range : ByteRange) (addr : Nat) (intent : AccessIntent)
    (perm : Permission) (readsInit : Bool) (writesInit : Bool)
    (effect : LedgerEffect := []) (atomic : Bool := false)
    (context : ContextId := thread₀) (authority : AuthorityEffect := []) :
    AccessDescriptor :=
  { context := context, address := .numeric (BitVec.ofNat 64 addr), space := .cpuVirtual
    provenance := prov, range := range
    intent := { intent with isAtomic := atomic }
    requiredPermission := perm, alignment := 1
    initialization := if readsInit then .allBytesInitialized else .readsNothing
    producesInitialized := writesInit
    ordering := if atomic then { atomicity := .atomic } else .plain
    admittedFaults := [.pageFault], ledgerEffect := effect
    authorityEffect := authority }

/-! ## Family one: a small load/store machine

Introduced without editing anything below it. There is no master sum type to
extend and no registry to register with; the family declares an instance and is
done. -/

/-- The first family's operation type. -/
inductive Alpha where
  /-- Load eight bytes from the buffer. -/
  | load
  /-- Store eight bytes to the buffer. -/
  | store
  /-- Atomically read and modify the buffer. -/
  | atomicAdd
  /-- Reserve the buffer, creating a release obligation. -/
  | reserve
  /-- Release the buffer, discharging it. -/
  | release
  /-- Divide by a value loaded from the buffer, faulting after the load. -/
  | divide
  /-- Store through the aliasing view. -/
  | storeThroughView
  /-- A store that declares only read-only permission. -/
  | badPermission
  /-- A store naming a range past the end of its allocation. -/
  | badRange
  /-- A store whose ledger effect would destroy a duty without discharging it. -/
  | badLedger
  /-- A well-formed store presenting an epoch the allocation has moved past. -/
  | staleEpoch
  /-- A store split across two substeps under a profile-owned visibility rule. -/
  | splitStore
  /-- The same split store, declared transactional. -/
  | atomicSplitStore
  /-- A device write that declares the program thread as its context, to defeat the
  race check. -/
  | impersonatingDmaWrite
  /-- A compute substep declaring a fault class the vocabulary never admitted. -/
  | computeWithPhantomFault
  /-- An operation declaring that it raises no faults, over an access that admits a
  page fault. Its two facets contradict each other. -/
  | faultsUnderdeclared
  /-- An operation declaring a fault class the vocabulary never admitted, with no
  compute substep to carry it — so `computeFaultNotRecognized` does not see it. -/
  | operationWithPhantomFault
  /-- An atomic store requesting an ordering mode this profile never registered. -/
  | unregisteredOrder
  /-- The same store requesting the mode the profile *does* register. -/
  | registeredOrder
  /-- A store claiming an ordering scope this profile never registered. -/
  | unregisteredScope
  /-- A sequence claiming a fault-visibility rule this profile never registered. -/
  | unregisteredVisibilityRule
  /-- A sequence claiming cross-substep atomicity under a target theorem this
  profile never registered. -/
  | unregisteredAtomicityClaim
  /-- A sequence claiming cross-substep atomicity under a name the profile
  registered as a *fault-visibility rule*, which is a different registry. -/
  | atomicityClaimFromTheWrongRegistry
  /-- An operation whose declared ordering is not the ordering its access
  requests. -/
  | orderingFacetDisagrees
  /-- An operation whose provenance claims a root extent the allocation does not
  have. -/
  | lyingRootExtent
  /-- An operation whose provenance claims an allocator the allocation was not
  produced by: the buffer came from `VirtualAlloc` and this names it an image
  mapping. Everything else is `store`, which commits. -/
  | lyingSource
  /-- An access-free operation declaring an ordering mode the profile never
  registered, so the per-access check cannot see it. -/
  | computeWithUnregisteredOrdering
  /-- A *load* of the read-only page declaring it needs write and execute
  permission the page does not grant. -/
  | overDeclaredPermission
  /-- A load reading uninitialized bytes under a rule this profile never
  registered. -/
  | unregisteredInitRule
  /-- The same load, under the rule the profile does register. -/
  | registeredInitRule
  /-- Discharges an obligation that was never live. -/
  | dischargeGhost
  /-- Joins two obligations that were never live into a new one. -/
  | joinGhosts
  /-- Splits a ghost obligation into two live-looking ones. -/
  | splitGhost
  /-- Two substeps, the first of which the state denies. -/
  | deniedThenStore
  /-- Discharges the release obligation while presenting authority under a
  protocol that does not govern it. -/
  | dischargeWithWrongAuthority
  /-- Writes the buffer through a borrowed slice, which requires a live loan. -/
  | writeThroughLoan
  /-- Writes a stack slot, which requires a live frame. -/
  | writeStackSlot
  /-- One effect containing two creates of the same initially-fresh identity,
  with distinguishable payloads. Each delta is individually applicable against
  the ledger as it stands before the effect runs. -/
  | createTwice
  /-- A store that also lends the buffer's head to the device engine. The first
  operation in this fixture that changes the authority map. -/
  | lendSlot
  /-- The same lend, naming the *engine* as lender while the program thread
  performs it: a context lending bytes it does not hold. -/
  | forgedLend
  /-- Two lends of the same identity in one effect, the second checked against the
  map the first left. -/
  | lendTwice
  /-- A store that also splits the loan the acting context holds. Stepped from a
  state where another context holds it, the same operation is the non-holder case. -/
  | splitLoan
  /-- A store that also returns the loan the acting context holds. -/
  | returnLoanSlot
  /-- A store that also joins two adjacent loans into one. -/
  | joinHalves
  /-- A store that also hands its loan to the device engine. -/
  | handOn
  /-- A store lending under a grant kind this profile never declared. -/
  | lendInventedKind
  /-- A store discharging the release duty under a protocol this profile never
  declared, with authority minted for it out of a string. -/
  | forgedProtocolRelease
  /-- A store handing the release duty to a context the machine has never seen. -/
  | handDutyToAStranger
  /-- The same, to the device engine, which the machine has seen. -/
  | handDutyToTheEngine
deriving DecidableEq, Repr

/-- The divide-error fault this family can raise. Named so the fixtures can
compare against the fault the transition recorded, rather than restating a
string. -/
def divideError : FaultClassId := ⟨⟨"divideError"⟩⟩

/-- The buffer protocol, and the authority this family holds under it. A real
family obtains this from its profile; the fixture mints one so the seam can be
exercised, which is exactly the gap `ProtocolAuthority`'s docstring records as an
M10 obligation. -/
def bufferProtocol : ObligationProtocolId := ⟨⟨"fake.buffer"⟩⟩

/-- Authority to act under `bufferProtocol`. -/
def bufferAuthority : ProtocolAuthority bufferProtocol :=
  .mintedBy bufferProtocol ⟨"fake.isa"⟩

/-- A different protocol, and authority under it. Used to show that authority for
one protocol does not authorize a duty governed by another. -/
def otherProtocol : ObligationProtocolId := ⟨⟨"fake.other"⟩⟩

/-- A protocol no profile in this file declares, and authority minted for it.

`ProtocolAuthority` is indexed by its protocol, so authority for one cannot be
*presented* for another — and `mintedBy` is public, total and unconditioned, so
authority for any protocol can be *minted* by anyone. Review built one exactly like
this in a module that owns nothing and discharged a duty this family had created
under its own protocol, with no violation recorded. -/
def forgedProtocol : ObligationProtocolId := ⟨⟨"attacker.no.such.protocol"⟩⟩

/-- The forged authority itself. Nothing about this value is ill-typed. -/
def forgedAuthority : ProtocolAuthority forgedProtocol :=
  .mintedBy forgedProtocol ⟨"attacker.no.such.profile"⟩

/-- Authority to act under `otherProtocol`, which governs nothing here. -/
def otherAuthority : ProtocolAuthority otherProtocol :=
  .mintedBy otherProtocol ⟨"fake.isa"⟩

/-- Two duties sharing one identity, distinguishable by kind. A single effect
creating both is the collision `LedgerEffectApplicable` must catch. -/
def collidingFirst : Obligation :=
  { id := collidingObligationId, kind := .releaseAllocation
    protocol := bufferProtocol, owner := thread₀ }

/-- The second, same identity and a different kind, so the two are telling
apart in the resulting ledger. -/
def collidingSecond : Obligation :=
  { id := collidingObligationId, kind := .closeHandle
    protocol := bufferProtocol, owner := thread₀ }

/-- The duty a fabricating delta would conjure. -/
def fabricatedObligation : Obligation :=
  { id := fabricatedObligationId, kind := .releaseAllocation
    protocol := bufferProtocol, owner := thread₀ }

/-- The release obligation `reserve` creates. -/
def releaseObligation : Obligation :=
  { id := releaseObligationId, kind := .releaseAllocation
    protocol := bufferProtocol, owner := thread₀ }

private def grants₀ : FreshSupply GrantTag := .initial

/-- A loan over the buffer, held by the program thread. -/
def bufferLoan : GrantId := grants₀.fresh.1

/-- A live call frame over the stack reservation. -/
def liveFrame : GrantId := grants₀.fresh.2.fresh.1

/-- A third identity, so a fixture can install two grants over one range. -/
def secondBufferLoan : GrantId := grants₀.fresh.2.fresh.2.fresh.1

/-- The identity an operation's declared lend uses. -/
def lentSlot : GrantId := grants₀.fresh.2.fresh.2.fresh.2.fresh.1

/-- The low half of a declared split. -/
def lowSlot : GrantId := grants₀.fresh.2.fresh.2.fresh.2.fresh.2.fresh.1

/-- The high half. -/
def highSlot : GrantId := grants₀.fresh.2.fresh.2.fresh.2.fresh.2.fresh.2.fresh.1

/-- A grant kind no profile in this file declares. `GrantKind` is open nominal, so
nothing stops an operation naming one; the vocabulary is what stops it being
admitted. -/
def inventedKind : GrantKind := ⟨⟨"fake.inventedAuthority"⟩⟩

/-- The grant an operation declares lending: the buffer's head, read-only, to the
device engine, lent by the program thread. -/
def declaredLoan : AuthorityGrant :=
  { kind := .loan, holder := engine₀, lender := thread₀, provenance := bufferProv
    range := ⟨0, 8⟩, rights := .readOnly }

/-- The first family's facet declaration. This is the whole of what a family
supplies; nothing else in the tree changes. -/
instance : HasOperationFacets Alpha where
  facets
    | .load =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite
            true false))
          faults := some [.pageFault], restartability := some .restartable
          ordering := some .plain }
    | .store =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .atomicAdd =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .readWrite .readWrite true true [] true with
              ordering := { atomicity := .atomic, order := .acquireRelease } })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some { atomicity := .atomic, order := .acquireRelease } }
    | .reserve =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.create bufferProtocol bufferAuthority releaseObligation]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .release =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge bufferProtocol bufferAuthority releaseObligationId]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .divide =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false)
                  , .compute [divideError] ]
              onFault := .priorEffectsVisible }
          faults := some [.pageFault, divideError], restartability := some .notRestartable
          ordering := some .plain }
    | .storeThroughView =>
        { memoryEffects := some (.single (acc viewProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .badPermission =>
        { memoryEffects := some (.single (acc constProv ⟨0, 8⟩ 0x2000 .write .readOnly
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .badRange =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 4096⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .badLedger =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.split bufferProtocol bufferAuthority releaseObligationId []]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .staleEpoch =>
        { memoryEffects := some (.single (acc staleProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .dischargeGhost =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge bufferProtocol bufferAuthority ghostObligationId]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .joinGhosts =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.join bufferProtocol bufferAuthority [ghostObligationId, ghostObligationId₂] fabricatedObligation]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .splitGhost =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.split bufferProtocol bufferAuthority ghostObligationId [fabricatedObligation]]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .writeThroughLoan =>
        { memoryEffects := some (.single (acc borrowedProv ⟨0, 8⟩ 0x4000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .writeStackSlot =>
        { memoryEffects := some (.single (acc frameProv ⟨0, 8⟩ 0x3000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .createTwice =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true
            [ .create bufferProtocol bufferAuthority collidingFirst
            , .create bufferProtocol bufferAuthority collidingSecond ]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .lendSlot =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [] false thread₀ [.issue lentSlot declaredLoan]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .forgedLend =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [] false thread₀
            [.issue lentSlot { declaredLoan with lender := engine₀ }]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .lendTwice =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [] false thread₀
            [.issue lentSlot declaredLoan, .issue lentSlot declaredLoan]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .splitLoan =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [] false thread₀ [.split bufferLoan lowSlot highSlot 32]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .returnLoanSlot =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [] false thread₀ [.returnGrant bufferLoan]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .joinHalves =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [] false thread₀ [.join bufferLoan secondBufferLoan lentSlot]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .handOn =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [] false thread₀ [.transfer bufferLoan engine₀]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .lendInventedKind =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [] false thread₀
            [.issue lentSlot { declaredLoan with kind := inventedKind }]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .forgedProtocolRelease =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true
            [.discharge forgedProtocol forgedAuthority releaseObligationId]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .handDutyToAStranger =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true
            [.transfer bufferProtocol bufferAuthority releaseObligationId engine₁]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .handDutyToTheEngine =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true
            [.transfer bufferProtocol bufferAuthority releaseObligationId engine₀]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .dischargeWithWrongAuthority =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [.discharge otherProtocol otherAuthority releaseObligationId]))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .deniedThenStore =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc staleProv ⟨0, 8⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨8, 8⟩ 0x1008 .write .readWrite false true) ]
              onFault := .priorEffectsVisible }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .splitStore =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .profileSpecific ⟨"fake.splitStore"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .impersonatingDmaWrite =>
        { memoryEffects := some (.single (acc viewProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true [] false thread₀))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .faultsUnderdeclared =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [], restartability := some .notRestartable
          ordering := some .plain }
    | .operationWithPhantomFault =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault, ⟨⟨"fake.neverDeclaredFault"⟩⟩]
          restartability := some .notRestartable, ordering := some .plain }
    | .unregisteredVisibilityRule =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .profileSpecific ⟨"fake.neverRegistered"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .unregisteredAtomicityClaim =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .transactional ⟨"fake.neverRegistered"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .atomicityClaimFromTheWrongRegistry =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .transactional ⟨"fake.splitStore"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .overDeclaredPermission =>
        { memoryEffects := some (.single (acc constProv ⟨0, 8⟩ 0x2000 .read
            { read := true, write := true, execute := true } true false))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .computeWithUnregisteredOrdering =>
        { memoryEffects := some
            { substeps := [ .compute [.pageFault] ]
              onFault := .priorEffectsVisible }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some { order := .profileSpecific ⟨"fake.neverRegistered"⟩ } }
    | .lyingRootExtent =>
        { memoryEffects := some (.single (acc
            { bufferProv with rootExtent := ⟨0, 4096⟩ } ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .lyingSource =>
        { memoryEffects := some (.single (acc
            { bufferProv with source := .imageMapping } ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .orderingFacetDisagrees =>
        { memoryEffects := some (.single (acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite
            false true))
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some { order := .acquire } }
    | .unregisteredInitRule =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false with
              initialization := .permitsUninitialized ⟨"fake.neverRegistered"⟩ })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .registeredInitRule =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false with
              initialization := .permitsUninitialized ⟨"fake.zeroedByLoader"⟩ })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }
    | .unregisteredOrder =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite false true [] true with
              ordering := { atomicity := .atomic
                            order := .profileSpecific ⟨"fake.neverRegistered"⟩ } })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some { atomicity := .atomic
                             order := .profileSpecific ⟨"fake.neverRegistered"⟩ } }
    | .registeredOrder =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite false true [] true with
              ordering := { atomicity := .atomic
                            order := .profileSpecific ⟨"fake.deviceRelease"⟩ } })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some { atomicity := .atomic
                             order := .profileSpecific ⟨"fake.deviceRelease"⟩ } }
    | .unregisteredScope =>
        { memoryEffects := some (.single
            { acc bufferProv ⟨0, 8⟩ 0x1000 .write .readWrite false true with
              ordering := { scope := .profileSpecific ⟨"fake.neverRegistered"⟩ } })
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some { scope := .profileSpecific ⟨"fake.neverRegistered"⟩ } }
    | .computeWithPhantomFault =>
        { memoryEffects := some
            { substeps := [ .compute [⟨⟨"fake.neverDeclaredFault"⟩⟩] ]
              onFault := .priorEffectsVisible }
          faults := some [⟨⟨"fake.neverDeclaredFault"⟩⟩]
          restartability := some .restartable, ordering := some .plain }
    | .atomicSplitStore =>
        { memoryEffects := some
            { substeps :=
                [ .access (acc bufferProv ⟨0, 4⟩ 0x1000 .write .readWrite false true)
                  , .access (acc bufferProv ⟨4, 4⟩ 0x1004 .write .readWrite false true) ]
              onFault := .transactional ⟨"fake.atomicSplitStore"⟩ }
          faults := some [.pageFault], restartability := some .notRestartable
          ordering := some .plain }

/-! ## Family two: an independently defined device family

Written as if by a different author. It shares no type with `Alpha`, does not
import it, and is packaged the same way. -/

/-- The second family's operation type. -/
inductive Beta where
  /-- A device engine writes the buffer. -/
  | dmaWrite
  /-- A device engine writes the far end of an alias chain: the same storage as
  the buffer, two declared hops away. -/
  | dmaWriteChained
  /-- A device engine discharges a duty the program thread holds. -/
  | dmaDischargesTheThreadsDuty
  /-- The engine writes the buffer's storage through a host-visible *device* view:
  the same declared storage, a different address space. -/
  | dmaWriteDeviceView
  /-- An operation that declares no memory effects at all. -/
  | undeclared
  /-- An operation that declares memory effects and faults but not restartability.

  `undeclared` cannot discriminate the closure gate: it is missing `memoryEffects`,
  and the branch immediately after the gate returns that same rejection for the same
  operation, so the gate could be switched off entirely with the fixture still green.
  This one is missing a facet no later branch asks about. -/
  | unrestartable
deriving DecidableEq, Repr

instance : HasOperationFacets Beta where
  facets
    | .dmaWrite =>
        { memoryEffects := some (.single
            { acc viewProv ⟨0, 8⟩ 0x1000 .write .readWrite false true
                (context := engine₀) with
              intent := { reads := false, writes := true } })
          faults := some [.pageFault, .deviceFault], restartability := some .notRestartable
          ordering := some .plain }
    | .dmaWriteChained =>
        { memoryEffects := some (.single
            { acc chainedProv ⟨0, 8⟩ 0x1000 .write .readWrite false true
                (context := engine₀) with
              intent := { reads := false, writes := true } })
          faults := some [.pageFault, .deviceFault], restartability := some .notRestartable
          ordering := some .plain }
    | .dmaDischargesTheThreadsDuty =>
        { memoryEffects := some (.single
            { acc borrowedProv ⟨0, 8⟩ 0x4000 .write .readWrite false true
                [.discharge bufferProtocol bufferAuthority releaseObligationId]
                (context := engine₀) with
              intent := { reads := false, writes := true } })
          faults := some [.pageFault, .deviceFault], restartability := some .notRestartable
          ordering := some .plain }
    | .dmaWriteDeviceView =>
        { memoryEffects := some (.single
            { acc deviceProv ⟨0, 8⟩ 0x1000 .write .readWrite false true
                (context := engine₀) with
              space := .deviceHostVisible
              intent := { reads := false, writes := true } })
          faults := some [.pageFault, .deviceFault], restartability := some .notRestartable
          ordering := some .plain }
    | .undeclared => {}
    | .unrestartable =>
        { memoryEffects := some (.single
            { acc viewProv ⟨0, 8⟩ 0x1000 .write .readWrite false true
                (context := engine₀) with
              intent := { reads := false, writes := true } })
          faults := some [.pageFault, .deviceFault]
          ordering := some .plain }

/-! ## The profile and the starting state -/

/-- The device's host-visible space. Numerically addressed, because
`AddressSpaceId.requiredRepresentation` says a device identity is, and not host
coherent, because §7.2 makes visibility explicit for device memory. -/
def deviceHostVisible64 : AddressSpace :=
  { id := .deviceHostVisible, repr := .numeric 64, memoryType := .notHostCached
    coherence := .requiresExplicitVisibility }

/--
A violation class this profile names for itself.

`AuthorityProvider.violationClass` is open nominal, so an authority a profile
adds can report a failure the generic transition has no name for: "there was no
live frame" is not "the loan state did not authorize this", and collapsing them
into `authorityUnavailable` would lose which authority was missing. Declaring it
below is what makes it usable — see `custom_violation_class_is_usable` and
`undeclared_provider_class_cannot_form_a_policy`.
-/
def frameAuthorityUnavailable : AuditViolationClass := ⟨⟨"fake.frameAuthorityUnavailable"⟩⟩

/-- The profile's address spaces, obligation kinds, and fault classes. -/
def vocabulary : AdmittedVocabulary :=
  { addressSpaces := ⟨[AddressSpace.cpuVirtual64, deviceHostVisible64]⟩
    faultClasses := ⟨[.pageFault, .deviceFault, divideError]⟩
    allocationSources :=
      ⟨[.virtualAlloc, .mappedFile, .imageMapping, .stack, .deviceMemory]⟩
    provenanceStepKinds := ⟨[]⟩
    auditViolationClasses :=
      ⟨AuditViolationClass.emittedByTransition ++ [frameAuthorityUnavailable]⟩
    obligationKinds := ⟨[.releaseAllocation, .closeHandle]⟩
    orderingModes := ⟨[⟨"fake.deviceRelease"⟩]⟩
    orderingScopes := ⟨[⟨"fake.queue"⟩]⟩
    initializationJustifications := ⟨[⟨"fake.zeroedByLoader"⟩]⟩
    atomicityJustifications := ⟨[⟨"fake.atomicSplitStore"⟩]⟩
    faultVisibilityRules := ⟨[⟨"fake.splitStore"⟩]⟩
    -- The kinds of authority this profile has. `GrantKind` is open nominal, so an
    -- operation minting one mints one named here: the fixtures lend and frame, and
    -- `docs/MEMORY_MODEL.md` §5.1's pin is not this profile's.
    grantKinds := ⟨[.loan, .frame]⟩
    -- The protocols this profile governs. `bufferProtocol` is its own;
    -- `otherProtocol` is declared so a fixture can present authority for a protocol
    -- that exists and does not govern the duty it names, which is a different
    -- failure from presenting one the profile never heard of.
    protocols := ⟨[bufferProtocol, otherProtocol]⟩ }

/-- A profile whose §10 package is explicitly unproved. It is a checklist of
propositions, not evidence for them, and this fixture does not pretend otherwise:
`RequiredProofPackage.Holds` is exactly what nothing here establishes. -/
def profile : MemoryProfile :=
  { id := ⟨"fake.isa"⟩, vocabularyVersion := 1, vocabulary := vocabulary
    package :=
      { accessDescriptorSoundness := True
        rangeProvenanceInitializationPreservation := preservationLaws
        permissionEnforcementAndFaultFidelity := True
        loanMapLaws := MemoryState.loanMapLaws
        consistencyGraphWellFormedness := True
        raceFreedomConsequences := True, synchronizationAndObligationTransfer := True
        allocatorFreshnessTeardownEpoch := MemoryState.allocatorLaws
        callStackFrameLifetime := True
        erasurePreservation := True, validationMetadata := True } }

/-! ## Two authority providers, authored outside `Grass/`

This is the extension test. `docs/MEMORY_MODEL.md` has several kinds of authority
— loans in §3, pins in §5.1, frame lifetimes in §6, lock tokens in §7.4, device
queue ownership in §7.5 — and a memory profile cannot enumerate them ahead of
time. The question is whether adding one costs a redesign of how operations are
packaged.

It does not. Both providers below are defined in this file. Neither
`AccessDescriptor`, `OperationFacets`, `HasOperationFacets`, `SomeOperation`, nor
the shape of `step` changes to accommodate them, and the operations that need
them declare their accesses exactly as every other operation does.

What this does *not* demonstrate is a loan or frame **model**. There is no split,
join, freeze, exclusivity-iff-empty, pinning, rebasing, or call-framing theorem
here; those are M3 and M4. The claim is about the seam, not about borrowing. -/

/-- A borrowed slice must be covered by a live grant of kind `loan`. -/
def loanProvider : AuthorityProvider where
  id := ⟨"fake.loan"⟩
  violationClass := .authorityUnavailable
  refuses memory d :=
    decide (d.provenance.root = borrowedAlloc) &&
    !decide (memory.GrantedOfKind .loan d.context d.provenance d.range d.intent)

/-- Stack storage must be covered by a live grant of kind `frame`. A distinct
provider over the same grant table, distinguished only by the grant kind it
demands — which is the point: two authority kinds, one mechanism. -/
def frameProvider : AuthorityProvider where
  id := ⟨"fake.frame"⟩
  violationClass := frameAuthorityUnavailable
  refuses memory d :=
    decide (d.provenance.root = stackAlloc) &&
    !decide (memory.GrantedOfKind .frame d.context d.provenance d.range d.intent)

/--
A provider whose violation class this profile never declared.

The adversary for `undeclared_provider_class_cannot_form_a_policy`. It is
well-typed and behaves like any other provider; the only thing wrong with it is
that its class is not in the vocabulary.
-/
def rogueProvider : AuthorityProvider where
  id := ⟨"fake.rogue"⟩
  violationClass := ⟨⟨"fake.undeclaredClass"⟩⟩
  refuses _ _ := true

/-! ## What this profile stores and what it would observe of the indeterminate

`Oracle.ofMemory` takes both as parameters rather than inventing either. -/

/-- What a store writes here: a pattern distinct from the zeros every allocation
starts with, so observing it after a store is evidence that the load read the
store's bytes rather than the initial contents. -/
def storedBytes : MachineState → AccessDescriptor → ByteSeq :=
  fun _ d => List.replicate d.range.size 0xAB

/-- What an indeterminate read would observe. No theorem below depends on its
value, but not for the reason an earlier version of this comment gave: every
allocation here starts fully initialized, so `byteAt?` never returns `none` and
the oracle never reaches this function at all. Nothing about denial ordering is
involved, and review corrected the claim. It is supplied because
`Oracle.ofMemory` requires it rather than defaulting it. -/
def indeterminateByte : MachineState → (d : AccessDescriptor) → Nat → Byte :=
  fun _ _ _ => 0xEE

/-- Every operation must declare its memory effects and its faults. -/
def policy : StepPolicy :=
  { profile := profile
    requiredFacets := [.memoryEffects, .faults, .restartability]
    oracle := .ofMemory storedBytes indeterminateByte
    authorities := [loanProvider, frameProvider]
    violationClassesDeclared := by decide
    vocabularyWellFormed := by decide }

/-- A vocabulary that declares one address-space identity twice is not well formed —
so no `StepPolicy` can be built from it. `find?` returns the first match, so without
this check which version an access was validated against would depend on list order.

**The two entries differ in memory type**, and they have differed in two other things
since: first in representation, which `AddressSpace.RepresentationMatchesIdentity` made
ill formed on its own, then in width, which `AddressSpace.WellFormed` did the same to.
Each time the fixture would have been refused for a reason that has nothing to do with
duplication. The memory type is a field nothing here constrains, which is what a
duplication fixture needs. Review found the original value — `repr := .symbolic` —
written down here and refused as a duplicate while the real defect, one such entry
declared alone, went through. -/
theorem duplicate_space_vocabulary_is_rejected :
    ¬ ({ vocabulary with
          addressSpaces := ⟨[ { id := .cpuVirtual, repr := .numeric 64
                                memoryType := .uncached, coherence := .hostCoherent }
                            , AddressSpace.cpuVirtual64 ]⟩ } :
        AdmittedVocabulary).WellFormed := by decide

/-- And each of those entries is well formed on its own, so the refusal above is the
duplication. -/
theorem each_duplicate_entry_is_well_formed_apart :
    ({ id := .cpuVirtual, repr := .numeric 64
       memoryType := .uncached, coherence := .hostCoherent } :
      AddressSpace).WellFormed ∧
    AddressSpace.cpuVirtual64.WellFormed := by
  exact ⟨by decide, by decide⟩

/-- **A vocabulary declaring `cpu.virtual` as symbolically addressed is not well
formed either**, which is the defect the duplicate fixture stood in front of. Declared
alone it passed, and against it `AccessDescriptor.WellFormedIn`'s alignment and
range-width clauses are both vacuous — review stepped a store of more than `2^64`
bytes at a symbolic address with a 4096-byte alignment demand. -/
theorem a_symbolic_cpu_space_vocabulary_is_rejected :
    ¬ ({ vocabulary with
          addressSpaces := ⟨[ { id := .cpuVirtual, repr := .symbolic
                                memoryType := .writeBack
                                coherence := .hostCoherent } ]⟩ } :
        AdmittedVocabulary).WellFormed := by decide

/-- Sixty-four initialized zero bytes: the starting contents of every allocation
in this fixture. Written through `ByteStore.write` with `initializes := true`
rather than assembled by hand, so the fixture's notion of initialized is the same
one `RangeInitialized` reads. -/
def zeroed64 : ByteStore := ByteStore.empty.write 0 (List.replicate 64 0) true

/-- The buffer, its aliasing view, and a read-only allocation. The alias is
declared here, in the state, because whether two allocations name the same bytes
is a fact about the machine and not about provenance. -/
def allocations₀ : List (AllocId × AllocationRecord) :=
  [ (bufferAlloc, { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
                    source := .virtualAlloc, owners := [engine₀, thread₀]
                    permission := .readWrite, live := true
                    bytes := zeroed64, base := some 0x1000 })
  , (viewAlloc, { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
                  source := .mappedFile, owners := [engine₀, thread₀]
                  permission := .readWrite, live := true
                  bytes := zeroed64, base := some 0x1000 })
  , (constAlloc, { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
                   source := .imageMapping, owners := [thread₀]
                   permission := .readOnly, live := true
                   bytes := zeroed64, base := some 0x2000 })
  , (stackAlloc, { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
                   source := .stack, owners := [engine₀, thread₀]
                   permission := .readWrite, live := true, bytes := zeroed64
                   base := some 0x3000 })
  , (borrowedAlloc, { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
                      source := .virtualAlloc, owners := [engine₀, thread₀]
                      permission := .readWrite, live := true, bytes := zeroed64
                      base := some 0x4000 })
  , (chainedAlloc, { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
                     source := .mappedFile, owners := [thread₀]
                     permission := .readWrite, live := true, bytes := zeroed64
                     base := some 0x1000 })
  , (deviceViewAlloc, { extent := ⟨0, 64⟩, epoch := epoch₀
                        space := .deviceHostVisible
                        source := .deviceMemory, owners := [engine₀, thread₀]
                        permission := .readWrite, live := true, bytes := zeroed64
                        base := some 0x1000 }) ]

def memory₀ : MemoryState :=
  (((MemoryState.empty.allocateAll? allocations₀).getD .empty).alias bufferAlloc viewAlloc).alias
    bufferAlloc deviceViewAlloc

/-- Every allocation happened, so `getD` did not fall back to the empty state. -/
theorem the_allocations_succeed :
    (MemoryState.empty.allocateAll? allocations₀).isSome := by decide

/-- The stack reservation the frame provider guards.

`viewAlloc` and `chainedAlloc` share `bufferAlloc`'s base, which is the point of
an alias: distinct allocation identities over the same storage. Placement does not
decide aliasing — `MemoryState.aliases` does, and `docs/MEMORY_MODEL.md` §2 makes
provenance rather than address the authority — so the two facts are declared
separately and agreeing here is the fixture being realistic rather than a rule. -/
def memory₁ : MemoryState := memory₀.alias viewAlloc chainedAlloc

/-- The starting machine state: allocations exist, but no authority is held. -/
def state₀ : MachineState := .initial memory₁

/-- The same state with both grants live. -/
def stateWithAuthority : MachineState :=
  { state₀ with
    memory :=
      (((state₀.memory.issue? bufferLoan
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := borrowedProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory).issue? liveFrame
        { kind := .frame, holder := thread₀, lender := engine₀, provenance := frameProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory }

/-- Both issues succeeded, so `getD` never fell back and the theorems below are
about a state that holds both grants. -/
theorem the_authority_issues_succeed :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := thread₀, lender := engine₀, provenance := borrowedProv
        range := ⟨0, 64⟩, rights := .readWrite }).isSome ∧
    (((state₀.memory.issue? bufferLoan
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := borrowedProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory).issue? liveFrame
        { kind := .frame, holder := thread₀, lender := engine₀, provenance := frameProv
          range := ⟨0, 64⟩, rights := .readWrite }).isSome := by
  exact ⟨by decide, by decide⟩

/-- The same state with the *engine* holding the buffer loan, so a fixture can ask
what a context that is not the holder may re-describe. -/
def stateWithEngineAuthority : MachineState :=
  { state₀ with
    memory := (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := borrowedProv
        range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory }

/-- That issue succeeded, so the refusal below is the actor rule and not an empty
map. -/
theorem the_engine_authority_issue_succeeds :
    (state₀.memory.issue? bufferLoan
      { kind := .loan, holder := engine₀, lender := thread₀, provenance := borrowedProv
        range := ⟨0, 64⟩, rights := .readWrite }).isSome ∧
    stateWithEngineAuthority.memory.grantAt? bufferLoan =
      some { kind := .loan, holder := engine₀, lender := thread₀, provenance := borrowedProv
             range := ⟨0, 64⟩, rights := .readWrite } := by
  exact ⟨by decide, by decide⟩

/-- The borrowed storage held as two adjacent halves by the program thread, so an
operation can join them. -/
def stateWithHalves : MachineState :=
  { state₀ with
    memory :=
      (((state₀.memory.issue? bufferLoan
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := borrowedProv
          range := ⟨0, 32⟩, rights := .readWrite }).getD state₀.memory).issue?
        secondBufferLoan
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := borrowedProv
          range := ⟨32, 32⟩, rights := .readWrite }).getD state₀.memory }

/-- Both halves are outstanding and adjacent, so the join fixture is about the join. -/
theorem the_halves_are_outstanding :
    (stateWithHalves.memory.grantAt? bufferLoan).isSome ∧
    (stateWithHalves.memory.grantAt? secondBufferLoan).isSome ∧
    stateWithHalves.memory.grantAt? lentSlot = Option.none := by
  exact ⟨by decide, by decide, by decide⟩

/-- Step one `Alpha` operation. -/
def stepAlpha (state : MachineState) (op : Alpha) : StepOutcome :=
  Grass.Op.step policy state (SomeOperation.of op) thread₀ .thread ⟨⟨"alpha"⟩⟩

/-- Step one `Beta` operation. Same function, different family. -/
def stepBeta (state : MachineState) (op : Beta) : StepOutcome :=
  Grass.Op.step policy state (SomeOperation.of op) engine₀ .dmaEngine ⟨⟨"beta"⟩⟩

/-! ## 1-5: the seam carries a new family end to end -/

/-- A load runs, records one event, and violates nothing. -/
theorem load_runs :
    ∃ s, (stepAlpha state₀ .load).state? = some s ∧ s.events.length = 1 ∧
      s.violations.IsEmpty := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> decide

/-- A store runs and violates nothing. -/
theorem store_runs :
    ∃ s, (stepAlpha state₀ .store).state? = some s ∧ s.violations.IsEmpty := by
  refine ⟨_, rfl, ?_⟩; decide

/-- An atomic read-modify-write runs, and its event records both a read and a
write. -/
theorem atomicAdd_is_a_read_modify_write :
    ∃ s e, (stepAlpha state₀ .atomicAdd).state? = some s ∧ s.events = [e] ∧
      e.event.kind = .readModifyWrite ∧ e.event.ordering.atomicity = .atomic := by
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩ <;> decide

/-! ## 4: obligations move through the same step -/

/-- Reserving creates the release obligation. -/
theorem reserve_creates_obligation :
    ∃ s, (stepAlpha state₀ .reserve).state? = some s ∧
      s.obligations.lookup releaseObligationId = some releaseObligation := by
  refine ⟨_, rfl, ?_⟩; decide

/-- Releasing after reserving discharges it, leaving nothing outstanding. -/
theorem reserve_then_release_discharges :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∃ t, (stepAlpha s .release).state? = some t ∧
        t.obligations.lookup releaseObligationId = Option.none := by
  intro s hs
  cases hs
  refine ⟨_, rfl, ?_⟩
  decide

/-! ## 6: invalid provenance, ranges, permissions, and ledger effects are rejected -/

/-- A store declaring read-only permission is not admitted: the profile refuses
the declaration before anything is attempted. -/
theorem badPermission_is_rejected :
    (stepAlpha state₀ .badPermission).rejection? = some .substepsNotWellFormed := by decide

/--
A range past the end of its allocation is caught at the declaration.

4096 bytes fit a 64-bit address space, so this is not the space check. It is
`rangeInProvenance`: the provenance declares a 64-byte root extent, and the range
escapes it. That condition used to be stated over an `Option` that was `none` for
a path-free provenance, which made it vacuous for exactly this shape — a
sixteen-exabyte access was well formed. This fixture is what keeps it closed.
-/
theorem badRange_is_rejected :
    (stepAlpha state₀ .badRange).rejection? = some .substepsNotWellFormed := by decide

/-- An access presenting a stale epoch is refused by the *state*, not by the
declaration: it is perfectly well formed, and the allocation it names has moved
on. The violation is recorded and nothing commits. -/
theorem staleEpoch_is_denied :
    ∃ s, (stepAlpha state₀ .staleEpoch).state? = some s ∧ ¬ s.violations.IsEmpty ∧
      s.events = [] := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> decide

/-- A ledger effect that would destroy a duty without discharging it is not
admitted. This is what makes `LedgerDelta.WellFormed` a mechanism: it is a
premise of admission, not a theorem with no consumer. -/
theorem badLedger_is_rejected :
    (stepAlpha state₀ .badLedger).rejection? = some (.accessNotAdmitted .ledgerEffectIllFormed) := by
  decide

/-! ## Obligations cannot be fabricated, dropped, or duplicated

`docs/OBLIGATIONS.md` §2 forbids all three, and `docs/FOUNDATION.md` law 7 states
the same rule as no obligation disappearance. Each of these was *performed* by an
earlier version of this transition: `LedgerDelta.WellFormed` checked only shape,
so a delta consuming an identity that was never live passed admission and the fold
applied it. -/

/-- Discharging a duty that is not live is refused. The earlier fold silently
no-opped, leaving no violation and no record. -/
theorem discharging_a_ghost_is_denied :
    ∀ s, (stepAlpha state₀ .dischargeGhost).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- Joining duties that were never live is refused. The earlier fold erased two
nothings and installed a duty from nowhere. -/
theorem joining_ghosts_is_denied :
    ∀ s, (stepAlpha state₀ .joinGhosts).state? = some s →
      s.obligations.lookup fabricatedObligationId = Option.none ∧
        s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- Splitting a duty that was never live is refused. -/
theorem splitting_a_ghost_is_denied :
    ∀ s, (stepAlpha state₀ .splitGhost).state? = some s →
      s.obligations.lookup fabricatedObligationId = Option.none ∧
        s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- Creating a duty whose identity is already live is refused, so a second
`create` cannot silently overwrite the first. -/
theorem creating_a_live_identity_is_denied :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .reserve).state? = some t →
        t.violations.recordCount = 1 := by
  intro s hs t ht
  cases hs; cases ht
  decide

/-! ## Authority is typed, and claimed authority must match the live duty

`ProtocolAuthority` is indexed by its protocol, so a `ProtocolAuthority
otherProtocol` cannot be passed where a `ProtocolAuthority bufferProtocol` is
expected — that half is the elaborator's, and there is no fixture for it because
the mistake does not typecheck. What a fixture *can* show is the state-level
half: a delta may present well-typed authority under a protocol that does not
govern the obligation it names, and `LedgerDelta.Applicable` refuses it.

An earlier version compared protocol identities only, which is comparing strings
any caller could write down, and carried no authority at all. -/

theorem wrong_protocol_authority_is_refused :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .dischargeWithWrongAuthority).state? = some t →
        t.obligations.lookup releaseObligationId = some releaseObligation ∧
          t.violations.recordCount = 1 := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- The same discharge with the governing protocol's authority succeeds, so the
refusal above is about the protocol and not about the discharge. -/
theorem right_protocol_authority_succeeds :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .release).state? = some t →
        t.obligations.lookup releaseObligationId = Option.none ∧
          t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-! ## Authority evidence extends the seam without redesigning it

Each pair is the same operation against two states differing only in whether the
grant is held. The refusal and the success both come out of `step`, through
providers this file defines. -/

/-- Without a loan, the borrowed write is refused and nothing commits. -/
theorem write_through_loan_is_refused_without_the_loan :
    ∀ s, (stepAlpha state₀ .writeThroughLoan).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- With the loan held, the same write commits. -/
theorem write_through_loan_succeeds_with_the_loan :
    ∀ s, (stepAlpha stateWithAuthority .writeThroughLoan).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## Reads observe writes

The M1 fixture ran against `Oracle.zeroed`, which reported the counts an intent
implied and supplied zero bytes of content. That was enough to exercise the
transition and not enough to say memory held anything. With `Oracle.ofMemory`
over `Grass/Memory/ByteStore.lean` the trace carries values that came from
somewhere. -/

/--
**A load observes the prior store.**

The store writes `0xAB` over bytes that began as `0x00`, and the load that
follows observes `0xAB`. Both facts are read off the recorded trace rather than
off memory, so this says the event model reports what the store committed and not
merely that the store changed a field.
-/
theorem a_load_observes_the_prior_store :
    ∃ s, (stepAlpha state₀ .store).state? = some s ∧
      ∃ t, (stepAlpha s .load).state? = some t ∧
        t.events.getLast?.bind (·.event.valueRead) = some (List.replicate 8 0xAB) :=
  ⟨_, rfl, _, rfl, by decide⟩

/-- Before the store, a load observes the zeros the allocation started with. The
control for the theorem above: without it, `0xAB` could have been what a load
always observes. -/
theorem a_load_before_the_store_observes_the_initial_bytes :
    ∃ s, (stepAlpha state₀ .load).state? = some s ∧
      s.events.getLast?.bind (·.event.valueRead) = some (List.replicate 8 0x00) :=
  ⟨_, rfl, by decide⟩

/-- A store leaves bytes outside its range alone. `MemoryState.write` goes
through `ByteStore.write`, and `ByteStore.cellAt?_write_of_not_covers` is the
framing law; this is that law observed through a real transition. -/
theorem a_store_leaves_neighbouring_bytes_alone :
    ∃ s, (stepAlpha state₀ .store).state? = some s ∧
      s.memory.byteAt? bufferAlloc 8 = some 0x00 ∧
      s.memory.byteAt? bufferAlloc 0 = some 0xAB :=
  ⟨_, rfl, by decide, by decide⟩

/-- A store to the buffer leaves the read-only allocation untouched, which is
`MemoryState.write_preserves_other_allocation` observed through a transition. -/
theorem a_store_leaves_other_allocations_alone :
    ∃ s, (stepAlpha state₀ .store).state? = some s ∧
      s.memory.byteAt? constAlloc 0 = some 0x00 :=
  ⟨_, rfl, by decide⟩

/-- Without a live frame, the stack write is refused. -/
theorem stack_write_is_refused_without_a_frame :
    ∀ s, (stepAlpha state₀ .writeStackSlot).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- With the frame live, the same write commits. -/
theorem stack_write_succeeds_with_a_frame :
    ∀ s, (stepAlpha stateWithAuthority .writeStackSlot).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/--
The two kinds do not substitute for one another.

A grant of kind `loan` over the stack reservation does not satisfy the frame
provider, so the two providers are genuinely distinct authorities over one table
rather than one authority wearing two names.
-/
theorem a_loan_is_not_a_frame :
    ((state₀.memory.issue? liveFrame
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := frameProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory).GrantedOfKind
        .loan thread₀ frameProv ⟨0, 8⟩ .write ∧
    ¬ ((state₀.memory.issue? liveFrame
        { kind := .loan, holder := thread₀, lender := engine₀, provenance := frameProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory).GrantedOfKind
        .frame thread₀ frameProv ⟨0, 8⟩ .write := by
  exact ⟨by decide, by decide⟩

/-! ## An authority cannot smuggle in a violation class the profile never declared

`AuthorityProvider.violationClass` is open nominal so that a profile can name its
own failures, and `refusalOf` records it directly. That is a hole unless the
class is required to be declared: a profile could add a provider with a fresh
class, and the transition would record a class outside the admitted vocabulary
while `docs/MEMORY_IMPLEMENTATION_PLAN.md` §3.11 claimed every emitted class was
declared. `docs/FOUNDATION.md` law 8 forbids exactly this shape of escape — the
open extension point is not permission to bypass the registry.

`StepPolicy.violationClassesDeclared` quantifies over
`AuthorityProvider.emittedClasses authorities`, which grows with the provider
list. The two theorems below are the two halves of the claim: a custom class that
is declared works, and one that is not cannot form a policy at all. -/

/--
A declared profile-specific class is usable.

`frameProvider` reports `frameAuthorityUnavailable`, which is not one of the
classes the generic transition emits. The vocabulary declares it, so `policy`
exists — this file would not compile otherwise. That the refusal actually
*records* the custom class rather than the generic `authorityUnavailable` is
`refused_stack_write_records_the_custom_class`, below.
-/
theorem custom_violation_class_is_usable :
    frameProvider.violationClass ∉ AuditViolationClass.emittedByTransition ∧
    frameProvider.violationClass ∈
      AuthorityProvider.emittedClasses policy.authorities ∧
    vocabulary.auditViolationClasses.Recognizes frameProvider.violationClass := by
  refine ⟨by decide, ?_, by decide⟩
  exact AuthorityProvider.mem_emittedClasses_of_provider (by simp [policy])

/--
**An undeclared provider class cannot form a `StepPolicy`.**

The `violationClassesDeclared` field is exactly this proposition, so a policy
whose providers include `rogueProvider` is unconstructible against this profile
— not merely ill-advised. Compare `custom_violation_class_is_usable`: the
difference between the two providers is declaration and nothing else.
-/
theorem undeclared_provider_class_cannot_form_a_policy :
    ¬ (∀ class_ ∈ AuthorityProvider.emittedClasses [loanProvider, rogueProvider],
        profile.vocabulary.auditViolationClasses.Recognizes class_) := by decide

/--
The refused stack write records the custom class.

Read off the ledger's public view, so this is the class an audit report would
show. Without it `custom_violation_class_is_usable` would only establish that the
class is *declarable*, not that anything ever emits it.
-/
theorem refused_stack_write_records_the_custom_class :
    ∀ s, (stepAlpha state₀ .writeStackSlot).state? = some s →
      s.violations.records?.map AuditViolation.class_ = [frameAuthorityUnavailable] := by
  intro s hs
  cases hs
  decide

/-- The rogue provider is rejected for its class alone. Its behaviour is
irrelevant — it never gets to run, because the policy that would consult it does
not exist. -/
theorem the_rogue_is_rejected_for_its_class_alone :
    ¬ vocabulary.auditViolationClasses.Recognizes rogueProvider.violationClass ∧
    (∀ class_ ∈ AuthorityProvider.emittedClasses [loanProvider],
      profile.vocabulary.auditViolationClasses.Recognizes class_) := by decide

/-- Authority is not ambient: a grant held by the device engine does not
authorize the program thread. -/
theorem authority_is_not_ambient :
    ((state₀.memory.issue? bufferLoan
        { kind := .loan, holder := engine₀, lender := thread₀, provenance := borrowedProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory).GrantedOfKind
        .loan engine₀ borrowedProv ⟨0, 8⟩ .write ∧
    ¬ ((state₀.memory.issue? bufferLoan
        { kind := .loan, holder := engine₀, lender := thread₀, provenance := borrowedProv
          range := ⟨0, 64⟩, rights := .readWrite }).getD state₀.memory).GrantedOfKind
        .loan thread₀ borrowedProv ⟨0, 8⟩ .write := by
  exact ⟨by decide, by decide⟩

/-! ## One effect cannot create the same identity twice

`LedgerDelta.Applicable` closes duplication per delta. That is not enough on its
own: an effect is a *sequence*, and checking every delta against the ledger as it
stood before the effect began lets two creates of one initially-fresh identity
both pass, after which the fold inserts one over the other and a duty is lost.
`docs/OBLIGATIONS.md` §2 forbids exactly that.

The two obligations below share an identity and differ in kind, so if the second
overwrote the first the resulting ledger would be observably wrong rather than
merely suspicious. -/

theorem both_creates_are_individually_applicable :
    LedgerDelta.Applicable ((FiniteMap.empty : FiniteMap ObligationId Obligation).domain)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.protocol)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.owner)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.kind) [thread₀, engine₀] thread₀
      (.create bufferProtocol bufferAuthority collidingFirst) ∧
    LedgerDelta.Applicable ((FiniteMap.empty : FiniteMap ObligationId Obligation).domain)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.protocol)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.owner)
      (fun id => ((FiniteMap.empty : FiniteMap ObligationId Obligation).lookup id).map
        Obligation.kind) [thread₀, engine₀] thread₀
      (.create bufferProtocol bufferAuthority collidingSecond) := by decide

/-- Together in one effect they are not applicable, because the second is checked
against the ledger the first left. -/
theorem the_pair_is_not_applicable :
    ¬ LedgerEffectApplicable (FiniteMap.empty : FiniteMap ObligationId Obligation)
      [thread₀, engine₀] thread₀
      [ .create bufferProtocol bufferAuthority collidingFirst
      , .create bufferProtocol bufferAuthority collidingSecond ] := by decide

/-- The transition refuses the operation, leaves the obligations untouched, and
records the violation. -/
theorem create_twice_is_refused :
    ∀ s, (stepAlpha state₀ .createTwice).state? = some s →
      s.obligations.lookup collidingObligationId = Option.none ∧
        s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-! ## A denied access stops the operation

An earlier `runAccesses` folded over every access unconditionally, so an operation
whose first substep was denied still committed its second. That is a
continue-after-denial policy no operation declared. -/

theorem denial_stops_the_operation :
    ∀ s, (stepAlpha state₀ .deniedThenStore).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/--
**A denial stops the operation on the faulting path too.**

`denial_stops_the_operation` covers the clean run. It did not cover the faulting
run, and the faulting run was broken: `runStep` performed the faulting substep's
access whether or not a survivor had been refused, so the denied first substep was
followed by a committed second one. Local adversarial review built exactly this
case and it went the other way.

Reported at substep 1, the surviving prefix is substep 0, which is denied for a
stale epoch. Nothing after it commits, and the store's bytes are untouched — the
last conjunct is the one that failed before, because counting events alone would
not have noticed a write that recorded no event.
-/
theorem denial_stops_the_operation_on_the_fault_path :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.deniedThenStore) thread₀
        .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 8
          else .none)).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.memory.byteAt? bufferAlloc 8 = some 0x00 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- And no fault is recorded, because the faulting substep was never reached.
`Op.runStep_records_no_fault_after_refusal` is the general form; recording one
here would be inventing a fault for a substep that did not run. -/
theorem a_denial_before_the_fault_records_no_fault :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.deniedThenStore) thread₀
        .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 8
          else .none)).state? = some s →
      s.faults = [] := by
  intro s hs
  cases hs
  decide

/-! ## A duty is discharged by its holder

`docs/OBLIGATIONS.md` opens by making an obligation a duty of "its holder" and §1
lists the owner as part of its form. `Obligation.owner` was carried, printed, and
consulted by nothing: `LedgerDelta.Applicable` checked liveness and protocol and
never ownership, so any context could discharge any duty. Local adversarial review
stepped a device engine through a discharge of the program thread's release
obligation and the duty vanished with no violation. -/

/-- The thread reserves, creating a duty it owns. -/
theorem the_thread_owns_what_it_reserved :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      (s.obligations.lookup releaseObligationId).map Obligation.owner = some thread₀ := by
  intro s hs
  cases hs
  decide

/-- **Another context cannot discharge it.** The duty survives and the attempt is
recorded, rather than the duty vanishing silently. -/
theorem another_context_cannot_discharge_it :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepBeta s .dmaDischargesTheThreadsDuty).state? = some t →
        (t.obligations.lookup releaseObligationId).isSome ∧ ¬ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- The holder still can, so the check is about ownership and not about refusing
every discharge. -/
theorem the_holder_can_discharge_it :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .release).state? = some t →
        t.obligations.lookup releaseObligationId = Option.none ∧ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-! ## An access cannot declare a context other than the one running it

`MemoryEvent.ofOutcome` takes the event's context identity from
`AccessDescriptor.context` and its kind from `step`'s argument, and nothing
compared them. `ConflictsWithHistory` discriminates on that identity, so
`docs/MEMORY_MODEL.md` §7.3's race rule was defeated by one field: a device write
naming the program thread aliased the thread's bytes and committed, and the event
it minted carried thread identity with engine kind, an incoherent pair §7.1
forbids. Two sources of truth for one fact. -/

/-- The honest device write is denied, which is the existing behaviour. -/
theorem the_honest_device_write_is_denied :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWrite).state? = some t →
        t.violations.recordCount = 1 := by
  intro s hs t ht
  cases hs
  cases ht
  decide

/-- The impersonating one is refused before it runs, rather than committing. -/
theorem an_impersonating_access_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.impersonatingDmaWrite) engine₀
      .dmaEngine ⟨⟨"alpha"⟩⟩ = .rejected (.contextMismatch thread₀ engine₀) := rfl

/-- The same descriptor run by the context it names is admitted *and commits*, so
the check compares rather than refusing anything unusual.

Asserting only that a state came back would not have said that: `staleEpoch_is_denied`
shows a denied access also produces a state. Review caught me reintroducing exactly
the weakness I had repaired two theorems earlier. -/
theorem the_named_context_may_run_it :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.impersonatingDmaWrite)
      thread₀ .thread ⟨⟨"alpha"⟩⟩).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/--
**One identity cannot be two kinds.**

`contextMismatch` closed the identity half: an access may not name a context other
than the one running it. The *kind* came from a separate `step` argument with
nothing relating it to anything, so the same `ContextId` could be stepped as a
thread once and a device engine the next time, and each event carried whatever
pair the caller supplied. `docs/MEMORY_MODEL.md` §7.1 requires identity and kind
together. `MachineState.contexts` records the pairing the first time a context is
seen, and disagreement is refused.
-/
theorem a_context_cannot_change_kind :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      Grass.Op.step policy s (SomeOperation.of Alpha.load) thread₀ .dmaEngine
        ⟨⟨"alpha"⟩⟩ = .rejected (.contextKindMismatch thread₀ .dmaEngine .thread) := by
  intro s hs
  cases hs
  rfl

/-- The same context under its own kind still runs, so the check is about
disagreement and not about refusing a second step. -/
theorem the_same_kind_still_runs :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepAlpha s .load).state? = some t →
        t.events.length = 2 ∧ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- And a fresh identity may take any kind, because the state has not seen it. -/
theorem a_fresh_context_may_take_any_kind :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWrite).state? = some t →
        (t.contexts.lookup engine₀) = some ContextKind.dmaEngine := by
  intro s hs t ht
  cases hs; cases ht
  decide

/-! ## A compute substep's fault classes are checked too

`AdmittedVocabulary.Admits` closes this for an access, quantifying over
`admittedFaults`. A compute substep has no descriptor, so `sequence.accesses`
never contains it and `Admits` never saw it: the only thing checked about one was
that its fault list is non-empty. `faultClassNotDeclared` then validated a plan
against a list that was itself unvalidated, and `.compute` is the constructor the
`div` case exists for. -/

theorem a_compute_substep_with_an_unrecognized_fault_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.computeWithPhantomFault) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.computeFaultNotRecognized ⟨⟨"fake.neverDeclaredFault"⟩⟩) := rfl

/-! ## A declared permission the page does not grant

`AccessDescriptor.requiredPermission` is "the page or section permission the access
requires", and its only consumer was `WellFormedIn.permissionSufficient`, which
checks it against the descriptor's own *intent*. `denialOf` checked the intent
against the page and never the declaration — so a load could declare it needs read,
write and execute on a read-only page and be admitted. A field whose only reader is
the descriptor that wrote it is a declaration nothing enforces, which is what this
layer deleted `AccessIntent.isDevice` and `AllocationRecord.initialized` for. -/

/-- **A permission the page does not grant is a violation**, even where the access's
intent alone would have been permitted. -/
theorem an_over_declared_permission_is_refused :
    ∀ s, (stepAlpha state₀ .overDeclaredPermission).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- And a load of the same page declaring only read commits, so the refusal is the
declaration and not the page. -/
theorem the_honest_permission_commits :
    ∀ s, (stepAlpha state₀ .load).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## Section 8's second conjunct, at this layer

§8 requires `VerifiedProgram` to prove the ledger empty **and that only spec-allowed
fault outcomes occur**. The first has `AuditViolationLedger.IsEmpty`; the second had
no predicate at all — `MachineState.faults` was appended to by `runStep` and read by
nothing under `Grass/`. `FaultsRecognized` is the half this layer can state. -/

/-- **A step that faults records a fault the profile declared.** -/
theorem a_raised_fault_is_recognized :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.load) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
          else .none)).state? = some s →
      s.faults.length = 1 ∧
      s.FaultsRecognized vocabulary.faultClasses.recognized := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- And the predicate discriminates: a state carrying a fault the profile never
declared does not satisfy it. Without this the theorem above would hold of a
predicate that is true of everything. -/
theorem an_undeclared_fault_is_not_recognized :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.load) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
          else .none)).state? = some s →
      ¬ s.FaultsRecognized [.deviceFault] := by
  intro s hs
  cases hs
  decide

/-! ## A split may not relabel a live duty

`LedgerDelta.Applicable`'s split clause pinned each output's protocol and owner and
not its `kind`, and allowed an output to reuse the source's identity. So a
one-element split, with a different kind, was legal: one duty in, one duty out,
relabelled, no `discharge` anywhere in the effect — and `docs/OBLIGATIONS.md` §3's
terminal disposition theorem would then report against the wrong duty. Identity reuse
also made this module's own statement of the M5 law ("no identity is produced that was
already live") false of deltas the checker accepted.

Both halves are closed, and the second needed the first's repair *and* a `kindOf`:
freshness alone left the relabelling legal under a new name, which review
demonstrated a second time. §3's split is one duty becoming several that together
cover the same duty, so every output carries the source's kind.

The fixtures below run against a ledger where the source is live, so a refusal is
about the split rather than about liveness — the earlier version of the first one
stepped an empty ledger and would have passed with no split rule at all. -/

/-- A ledger holding the release duty. -/
private def ledger₁ : FiniteMap ObligationId Obligation :=
  (FiniteMap.empty : FiniteMap ObligationId Obligation).insert releaseObligationId
    releaseObligation

/-- The source is live here, and its kind is the one a faithful split must carry. -/
theorem the_split_source_is_live :
    ledger₁.lookup releaseObligationId = some releaseObligation ∧
      releaseObligation.kind = .releaseAllocation := by decide

/-- **A split onto the source's own identity is refused** — the freshness half. -/
theorem a_relabelling_split_is_refused :
    ¬ Grass.Op.LedgerEffectApplicable ledger₁ [thread₀, engine₀] thread₀
      [.split bufferProtocol bufferAuthority releaseObligationId
        [{ id := releaseObligationId, kind := .closeHandle
           protocol := bufferProtocol, owner := thread₀ }]] := by decide

/-- **A split onto a fresh identity with a different kind is refused too** — the half
freshness does not catch, and the one that mattered. -/
theorem a_relabelling_split_under_a_fresh_id_is_refused :
    ¬ Grass.Op.LedgerEffectApplicable ledger₁ [thread₀, engine₀] thread₀
      [.split bufferProtocol bufferAuthority releaseObligationId
        [{ id := ghostObligationId, kind := .closeHandle
           protocol := bufferProtocol, owner := thread₀ }]] := by decide

/-- The same split keeping the source's kind is applicable, so the two refusals above
are the identity and the kind and not some other clause. -/
theorem a_faithful_split_is_applicable :
    Grass.Op.LedgerEffectApplicable ledger₁ [thread₀, engine₀] thread₀
      [.split bufferProtocol bufferAuthority releaseObligationId
        [{ id := ghostObligationId, kind := .releaseAllocation
           protocol := bufferProtocol, owner := thread₀ }]] := by decide

/-- **A join may not relabel either**, and the same pair of fixtures says so from the
other direction: joining a `releaseAllocation` duty into a `closeHandle` one is
refused, and into a duty of its own kind is not. -/
theorem a_relabelling_join_is_refused :
    ¬ Grass.Op.LedgerEffectApplicable ledger₁ [thread₀, engine₀] thread₀
      [.join bufferProtocol bufferAuthority [releaseObligationId]
        { id := ghostObligationId, kind := .closeHandle
          protocol := bufferProtocol, owner := thread₀ }] := by decide

theorem a_faithful_join_is_applicable :
    Grass.Op.LedgerEffectApplicable ledger₁ [thread₀, engine₀] thread₀
      [.join bufferProtocol bufferAuthority [releaseObligationId]
        { id := ghostObligationId, kind := .releaseAllocation
          protocol := bufferProtocol, owner := thread₀ }] := by decide

/-- A second live duty of the same kind, protocol and owner, so a fixture can join
two of them. `Obligation` carries nothing else, so these two are as alike as the type
permits. -/
def secondReleaseObligation : Obligation :=
  { id := ghostObligationId, kind := .releaseAllocation
    protocol := bufferProtocol, owner := thread₀ }

/-- Both duties live. -/
private def ledger₂ : FiniteMap ObligationId Obligation :=
  ledger₁.insert ghostObligationId secondReleaseObligation

/-- **A join onto a live identity is refused.** The freshness half of the join
clause, which review mutation-tested and found unfixtured: deleting `into.id ∉ live`
from `LedgerDelta.Applicable` left the whole build green, and a probe then joined one
source onto a live identity and watched `applyDelta`'s insert overwrite a duty —
§2's "dropping", silently. The docstring here and the plan both said the split twin
was fixtured; review checked and it was not — see `a_relabelling_split_is_refused`
below, whose outputs also carry the wrong kind. -/
theorem a_join_onto_a_live_identity_is_refused :
    ¬ Grass.Op.LedgerEffectApplicable ledger₂ [thread₀, engine₀] thread₀
      [.join bufferProtocol bufferAuthority [releaseObligationId]
        secondReleaseObligation] := by decide

/-- And the same join onto a fresh identity is applicable, so the refusal above is
freshness and not something else in the clause. -/
theorem a_join_onto_a_fresh_identity_is_applicable :
    Grass.Op.LedgerEffectApplicable ledger₂ [thread₀, engine₀] thread₀
      [.join bufferProtocol bufferAuthority [releaseObligationId]
        { secondReleaseObligation with id := fabricatedObligationId }] := by decide

/-! ## The six ledger clauses a mutation sweep found unguarded

Review replaced each clause of `LedgerDelta.Applicable` and `LedgerDelta.WellFormed`
with a vacuous equivalent, one at a time, and rebuilt. Six survived: `create`'s
protocol agreement, `split`'s owner and freshness clauses, `join`'s owner clause, and
both `Nodup` conditions. The controls in the same sweep were caught, so the sweep was
discriminating and these six were the gap.

`docs/OBLIGATIONS.md` §2 is what each of them holds: "Dropping, duplicating, or
fabricating obligations is forbidden." Without `split`'s owner clause the engine can
step a split of the thread's live duty into duties it owns itself, which is §2's
transfer under another name with no violation recorded. Without either `Nodup` a
single duty is counted as two -- the duplication half -- and `applyDelta`'s fold then
collapses the pair back into one row.

Each pair below varies one thing. Where the varying thing is ownership the *source*
changes rather than the actor, because an output's owner must equal the actor too, so
varying the actor would move two clauses at once. -/

/-- The same duty shape, owned by the engine, so an ownership pair can hold the actor
fixed. -/
def engineObligation : Obligation :=
  { id := ghostObligationId₂, kind := .releaseAllocation
    protocol := bufferProtocol, owner := engine₀ }

/-- Both thread duties and the engine's, all live. -/
private def ledger₃ : FiniteMap ObligationId Obligation :=
  ledger₂.insert ghostObligationId₂ engineObligation

/-- The three sources this section splits and joins are live and differ in owner
alone, so the refusals below are the owner clauses and not liveness. -/
theorem the_ledger_three_sources_are_live :
    (ledger₃.lookup releaseObligationId).map Obligation.owner = some thread₀ ∧
    (ledger₃.lookup ghostObligationId₂).map Obligation.owner = some engine₀ ∧
    (ledger₃.lookup releaseObligationId).map Obligation.kind =
      (ledger₃.lookup ghostObligationId₂).map Obligation.kind ∧
    (ledger₃.lookup releaseObligationId).map Obligation.protocol =
      (ledger₃.lookup ghostObligationId₂).map Obligation.protocol := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **A create whose duty names another protocol is refused.** §2 gives a protocol
authority over its own obligations and no others; without this clause a step holding
`bufferAuthority` could mint a duty governed by `fake.other` and no protocol theorem
would ever be asked about it. -/
theorem a_create_under_another_protocol_is_refused :
    ¬ Grass.Op.LedgerEffectApplicable ledger₁ [thread₀, engine₀] thread₀
      [.create bufferProtocol bufferAuthority
        { id := fabricatedObligationId, kind := .releaseAllocation
          protocol := otherProtocol, owner := thread₀ }] := by decide

/-- The same create under its own protocol is applicable, so the refusal is the
protocol clause. -/
theorem the_same_create_under_its_own_protocol_is_applicable :
    Grass.Op.LedgerEffectApplicable ledger₁ [thread₀, engine₀] thread₀
      [.create bufferProtocol bufferAuthority
        { id := fabricatedObligationId, kind := .releaseAllocation
          protocol := bufferProtocol, owner := thread₀ }] := by decide

/-- The outputs both split fixtures below produce: fresh, of the source's kind, owned
by the engine. -/
def engineSplitOutput : Obligation :=
  { id := fabricatedObligationId, kind := .releaseAllocation
    protocol := bufferProtocol, owner := engine₀ }

/-- **The engine may not split a duty the thread owns.** §1 makes an obligation a duty
of its holder, and this is the clause that says so for `split`. Without it the engine
steps this and walks away owning both halves of somebody else's duty. -/
theorem a_split_of_another_contexts_duty_is_refused :
    ¬ Grass.Op.LedgerEffectApplicable ledger₃ [thread₀, engine₀] engine₀
      [.split bufferProtocol bufferAuthority releaseObligationId
        [engineSplitOutput]] := by decide

/-- The same split of the engine's own duty is applicable. One field of the delta
changes -- the source identity -- and the two sources are live, of one kind and one
protocol, by `the_ledger_three_sources_are_live`. -/
theorem the_same_split_of_its_own_duty_is_applicable :
    Grass.Op.LedgerEffectApplicable ledger₃ [thread₀, engine₀] engine₀
      [.split bufferProtocol bufferAuthority ghostObligationId₂
        [engineSplitOutput]] := by decide

/-- **A split onto a live identity is refused** -- the freshness half, and the twin
that `a_join_onto_a_live_identity_is_refused`'s docstring claimed was already
fixtured. It was not: the two relabelling fixtures above give their outputs a kind the
source does not have, so the kind clause refuses them and the freshness clause could
be deleted with the tree green. Here the kind matches. -/
theorem a_split_onto_a_live_identity_is_refused :
    ¬ Grass.Op.LedgerEffectApplicable ledger₂ [thread₀, engine₀] thread₀
      [.split bufferProtocol bufferAuthority releaseObligationId
        [secondReleaseObligation]] := by decide

/-- And onto a fresh identity it is applicable, so the refusal is freshness. -/
theorem the_same_split_onto_a_fresh_identity_is_applicable :
    Grass.Op.LedgerEffectApplicable ledger₂ [thread₀, engine₀] thread₀
      [.split bufferProtocol bufferAuthority releaseObligationId
        [{ secondReleaseObligation with id := fabricatedObligationId }]] := by decide

/-- **The engine may not join a duty the thread owns**, for the same reason as
`split`. -/
theorem a_join_of_another_contexts_duty_is_refused :
    ¬ Grass.Op.LedgerEffectApplicable ledger₃ [thread₀, engine₀] engine₀
      [.join bufferProtocol bufferAuthority [releaseObligationId]
        engineSplitOutput] := by decide

/-- The same join of the engine's own duty is applicable. -/
theorem the_same_join_of_its_own_duty_is_applicable :
    Grass.Op.LedgerEffectApplicable ledger₃ [thread₀, engine₀] engine₀
      [.join bufferProtocol bufferAuthority [ghostObligationId₂]
        engineSplitOutput] := by decide

/-! ### Shape, which `StepPolicy.Admits` checks and `LedgerEffectApplicable` does not

`LedgerDelta.WellFormed` is the other half and the two `Nodup` conditions live there,
so these four are stated over it directly rather than through the transition. -/

/-- **A split producing one identity twice is not well formed.** §2's "duplicating":
`applyDelta` folds the outputs in, so the second insert overwrites the first and a
duty claimed as two becomes one row. -/
theorem a_split_producing_one_identity_twice_is_ill_formed :
    ¬ (LedgerDelta.split bufferProtocol bufferAuthority releaseObligationId
      [engineSplitOutput, engineSplitOutput]).WellFormed := by decide

/-- Two distinct outputs are well formed, so the refusal is the duplication and not
the count. -/
theorem a_split_producing_two_identities_is_well_formed :
    (LedgerDelta.split bufferProtocol bufferAuthority releaseObligationId
      [engineSplitOutput,
       { engineSplitOutput with id := ghostObligationId₂ }]).WellFormed := by decide

/-- **A join consuming one identity twice is not well formed**, which is the same
sentence read from the other side: one duty counted as two sources. -/
theorem a_join_consuming_one_identity_twice_is_ill_formed :
    ¬ (LedgerDelta.join bufferProtocol bufferAuthority
      [releaseObligationId, releaseObligationId] engineSplitOutput).WellFormed := by
  decide

/-- Two distinct sources are well formed. -/
theorem a_join_consuming_two_identities_is_well_formed :
    (LedgerDelta.join bufferProtocol bufferAuthority
      [releaseObligationId, ghostObligationId] engineSplitOutput).WellFormed := by
  decide

/-- **And here is what a join of two independent duties does**, which is a gap rather
than a guard.

`Applicable`'s join clause requires the sources to be live, to share the claimed
protocol, to be owned by the actor, and to carry the output's kind. Two duties that
are independent in every sense the model can express satisfy all four, because
`Obligation` carries no payload: nothing says *what* a duty covers, so nothing can
say that an output covers what its sources covered. §2's join is "several obligations
become one, together covering the same duty", and "together covering" is the part
this layer cannot represent.

So two live duties join into one and a single discharge ends both. Review found it;
it is here so the gap is visible in compiled code rather than only in a plan, and so
that closing it — which means giving `Obligation` a coverage payload — breaks this
theorem rather than passing unnoticed. -/
theorem a_join_of_two_duties_halves_the_ledger :
    ledger₂.domain.length = 2 ∧
    Grass.Op.LedgerEffectApplicable ledger₂ [thread₀, engine₀] thread₀
      [.join bufferProtocol bufferAuthority [releaseObligationId, ghostObligationId]
        { secondReleaseObligation with id := fabricatedObligationId }] ∧
    ((Grass.Op.applyLedgerEffect? ledger₂ [thread₀, engine₀] thread₀
      [.join bufferProtocol bufferAuthority [releaseObligationId, ghostObligationId]
        { secondReleaseObligation with id := fabricatedObligationId }]).map
      (fun ledger => ledger.domain.length)) = some 1 := by
  exact ⟨by decide, by decide, by decide⟩

/-! ## A provenance that lies about its root's extent

`AccessDescriptor.WellFormedIn.rangeInProvenance` bounds an access by
`Provenance.rootExtent`, and nothing compared that to the allocation table — so a
descriptor supplied the bound it was checked against, and a write far outside a
64-byte allocation was well formed. `denialOf`'s own extent check caught the write
incidentally as `outOfBounds`, which reports the wrong rule: the access was not
outside the bounds it declared, it declared the wrong bounds. -/

/-- **A lying root extent is a violation of its own.** The access here is inside
the allocation, so nothing else would have caught it. -/
theorem a_lying_root_extent_is_recorded :
    ∀ s, (stepAlpha state₀ .lyingRootExtent).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.violations.records?.any (fun r => r.class_ = .provenanceExtentMismatch) := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-! ## A provenance that lies about where its storage came from

`docs/MEMORY_MODEL.md` §2 asks a profile to distinguish sources such as
`VirtualAlloc`, process heap, `malloc`, page-table mapping, kernel heap, bump
allocator, stack, mapped file and device memory. `Provenance.source` recorded which
one a descriptor claimed and the state held no counterpart, so the claim was
unfalsifiable: two provenances differing only in `source` were the same storage to
every rule in the layer. `AllocationRecord.source` is the counterpart. -/

/-- **A lying source is a violation of its own.** The access is in bounds, in the
right space, at the declared address, with sufficient permission -- every other
clause of `denialOf` passes, so nothing else would have caught it. -/
theorem a_lying_source_is_recorded :
    ∀ s, (stepAlpha state₀ .lyingSource).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.violations.records?.any (fun r => r.class_ = .provenanceSourceMismatch) := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- **The lie is one field.** `lyingSource`'s provenance is `store`'s with the source
replaced, and restoring it recovers `store`'s exactly -- so the refusal above cannot
be blamed on any other part of the provenance. `the_honest_extent_commits` below is
the positive control: it steps `.store`, which commits with no violation. -/
theorem the_lie_is_only_the_source :
    { ({ bufferProv with source := .imageMapping } : Provenance) with
      source := .virtualAlloc } = bufferProv ∧
    ({ bufferProv with source := .imageMapping } : Provenance) ≠ bufferProv := by
  exact ⟨by decide, by decide⟩

/-- The same access with the honest extent commits, so the violation above is the
`rootExtent` clause and not the range. -/
theorem the_honest_extent_commits :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## A justification the profile never registered is rejected

`INSTRUCTIONS.md` §4 wants a target theorem behind a cross-substep atomicity claim,
`MEMORY_MODEL.md` §4 wants a profile rule behind an uninitialized read, and §7.1
wants a profile behind a fault-visibility rule it owns. All three were names and
nothing held them: a sequence got all-or-nothing fault semantics, and an access
read uninitialized bytes, by declaring a string.

Three registries rather than one. A rule permitting an uninitialized read is not a
proof that a two-substep store is all-or-nothing, and one namespace would let
either name satisfy the other — two facts in one carrier is what this layer removed
from `AccessIntent.isDevice`. -/

/-- **An unregistered fault-visibility rule is refused.** -/
theorem an_unregistered_visibility_rule_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredVisibilityRule) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.onFaultRuleNotRegistered ⟨"fake.neverRegistered"⟩) := rfl

/-- **An unregistered atomicity claim is refused**, and it is checked against a
*different* registry: the name below is registered as a visibility rule and still
does not satisfy a `transactional` claim. -/
theorem an_unregistered_atomicity_claim_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredAtomicityClaim) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.onFaultRuleNotRegistered ⟨"fake.neverRegistered"⟩) := rfl

/--
**A name registered in the other registry does not satisfy the claim.**

The fixture that pins separation, and it was missing for a round: the theorems above
cite `fake.neverRegistered`, which is in neither registry, so they hold equally of an
implementation that consults both. Review patched `unregisteredOnFaultRule?` to
accept a name found in *either* — the shared namespace the commit message said was
pinned against — and the whole suite stayed green.

`fake.splitStore` is registered as a fault-visibility rule and is refused as an
atomicity claim.
-/
theorem a_name_from_the_wrong_registry_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicityClaimFromTheWrongRegistry)
      thread₀ .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.onFaultRuleNotRegistered ⟨"fake.splitStore"⟩) := rfl

/-- And the same name *is* accepted where it belongs, so the refusal above is about
the registry rather than about the name. -/
theorem the_registries_hold_what_they_should :
    vocabulary.faultVisibilityRules.Recognizes ⟨"fake.splitStore"⟩ ∧
    ¬ vocabulary.atomicityJustifications.Recognizes ⟨"fake.splitStore"⟩ ∧
    ¬ vocabulary.faultVisibilityRules.Recognizes ⟨"fake.atomicSplitStore"⟩ ∧
    (stepAlpha state₀ .splitStore).state?.isSome ∧
    (stepAlpha state₀ .atomicSplitStore).state?.isSome := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **An uninitialized read under an unregistered rule is not admitted.** -/
theorem an_unregistered_initialization_rule_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredInitRule) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.accessNotAdmitted
        (.initializationRuleNotRegistered ⟨"fake.neverRegistered"⟩)) := rfl

/-- And the registered rule is admitted, so the refusal is about the registry
rather than about `permitsUninitialized` being refused outright. -/
theorem the_registered_initialization_rule_is_admitted :
    (stepAlpha state₀ .registeredInitRule).state?.isSome := by decide

/-! ## An ordering mode the profile never registered is rejected

`docs/MEMORY_MODEL.md` §7.1 fixes five portable modes and four portable scopes and
allows a profile its own, and says an unsupported mapping is rejected. Nothing
rejected one: `MemoryOrder.IsPortable` had no consumer, `AdmittedVocabulary` had no
ordering registry, and an access declaring `profileSpecific` with any name at all
stepped and minted an event carrying it. -/

/-- **An unregistered ordering mode is not admitted.** -/
theorem an_unregistered_order_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredOrder) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.accessNotAdmitted (.orderNotRegistered ⟨"fake.neverRegistered"⟩)) := rfl

/-- **The registered mode is admitted**, so the rejection above is about the
registry rather than about profile-specific modes being refused outright. Without
this the theorem above would be consistent with rejecting every non-portable
mode. -/
theorem the_registered_order_is_admitted :
    (stepAlpha state₀ .registeredOrder).state?.isSome := by decide

/-- **An unregistered scope is not admitted either.** A device fence claiming a
scope nobody defined is not a weaker fence; it is an undefined one. -/
theorem an_unregistered_scope_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredScope) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.accessNotAdmitted (.scopeNotRegistered ⟨"fake.neverRegistered"⟩)) := rfl

/-- **The three name a different clause each**, which is the point of reporting a
reason: an unregistered ordering mode, an unregistered scope and an unregistered
initialization rule were one indistinguishable `accessNotAdmitted`, and the three
theorems above asserted a constructor any admissibility failure satisfies. -/
theorem the_three_refusals_are_distinguishable :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredOrder) thread₀
      .thread ⟨⟨"alpha"⟩⟩).rejection? ≠
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredScope) thread₀
      .thread ⟨⟨"alpha"⟩⟩).rejection? ∧
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredScope) thread₀
      .thread ⟨⟨"alpha"⟩⟩).rejection? ≠
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.unregisteredInitRule) thread₀
      .thread ⟨⟨"alpha"⟩⟩).rejection? := by
  exact ⟨by decide, by decide⟩

/-- **A portable mode needs no registration**, exercised on a mode that is not
`relaxed`: `atomicAdd` requests `acquireRelease` and the profile registers only
`fake.deviceRelease`.

An earlier version of this theorem asserted `¬ Recognizes ⟨"acquireRelease"⟩`, which
is true of every possible implementation — `AdmitsOrder` never looks a portable mode
up, and `"acquireRelease"` is not how a `MemoryOrder` constructor would be spelled in
a registry in any case — and paired it with a step of an operation whose descriptor
requested `relaxed`, the same mode as every other fixture in the file. It could not
have failed. -/
theorem a_portable_order_needs_no_registration :
    vocabulary.AdmitsOrder (.acquireRelease) ∧
    vocabulary.orderingModes.recognized = [⟨"fake.deviceRelease"⟩] ∧
    (stepAlpha state₀ .atomicAdd).state?.isSome := by
  exact ⟨by decide, by decide, by decide⟩

/-- **An access-free operation's ordering declaration is checked too.**

Checking the operation's ordering only through its accesses is vacuous for a
sequence with none, and review stepped a `.compute`-only operation declaring
`MemoryOrder.profileSpecific` with a name in no registry. -/
theorem an_access_free_operation_cannot_hide_its_ordering :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.computeWithUnregisteredOrdering)
      thread₀ .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.operationOrderingNotRegistered ⟨"fake.neverRegistered"⟩) := rfl

/-- **The operation's own ordering declaration is checked against its accesses.**
`OperationFacets.ordering` was the second facet consumed by nothing, and six of this
fixture's operations declared an ordering their accesses did not request. -/
theorem an_operation_whose_ordering_disagrees_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.orderingFacetDisagrees) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.operationOrderingDisagrees { order := .acquire } .plain) := rfl

/-! ## And so is the operation's own fault declaration

`OperationFacets.faults` was consumed by nothing. `OperationFacets.supplied` reads
only `isSome`, so an operation declaring `faults := some []` closed the facet and
then page-faulted through a substep that admitted one — the substep-level list was
checked, the operation-level list above it was checked against nothing. That is a
fact the model carries and nothing consults, which is the shape this layer removed
from `AllocationRecord.initialized` and `AccessIntent.isDevice`.

Eighteen of this fixture's own operations were inconsistent when the check went in,
which is how little a declaration nobody reads constrains. -/

/-- **An operation that declares no faults, over an access that admits one, is
refused.** Refused statically, before any fault plan is supplied, because the two
declarations contradict each other and law 8's answer to that is not to pick one. -/
theorem an_underdeclared_operation_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.faultsUnderdeclared) thread₀
      .thread ⟨⟨"alpha"⟩⟩ = .rejected (.operationFaultsIncomplete .pageFault) := rfl

/-- And it is refused with no fault plan at all, so this is a check on the
declaration rather than on what the machine did. -/
theorem an_underdeclared_operation_is_refused_without_a_fault :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.faultsUnderdeclared) thread₀
      .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun _ => .none)).Ran = False := by
  decide

/-- **An operation declaring a fault class the vocabulary never admitted is
refused**, with no compute substep involved — that was the only other place an
unrecognized class was caught, and this operation has none. -/
theorem an_operation_with_a_phantom_fault_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.operationWithPhantomFault) thread₀
      .thread ⟨⟨"alpha"⟩⟩ =
      .rejected (.operationFaultNotRecognized ⟨⟨"fake.neverDeclaredFault"⟩⟩) := rfl

/-- An operation may declare *more* than its substeps can raise, so the check is
containment and not equality: the device operations declare `[.pageFault,
.deviceFault]` over accesses that admit only the first, and they run.

`store` used to be cited here, and it declares exactly what its access admits — an
equality case, which cannot distinguish containment from equality. Review
strengthened the check to equality and only the device operations failed, so they
are the ones that pin it. -/
theorem a_declaration_wider_than_the_substeps_still_runs :
    (stepBeta state₀ .dmaWrite).state?.isSome ∧
    (stepAlpha state₀ .store).state?.isSome := by
  exact ⟨by decide, by decide⟩

/-- `divide`'s compute substep declares `divideError`, which the vocabulary does
recognize, so it still runs *and commits its load*. Same reason as
`the_named_context_may_run_it`: "produced a state" is satisfied by a denial. -/
theorem a_recognized_compute_fault_still_runs :
    ∀ s, (stepAlpha state₀ .divide).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## What a fault plan may claim

Three things the transition took on trust from its caller and now checks. Each was
found by local adversarial review, and each is the shape law 8 targets: an
unchecked input is not rejected, it is modelled. -/

/-- A fault class no substep declares is refused, not recorded.

`Substep.faults` has always said what a step may raise and `AdmittedVocabulary.Admits`
has always required an access's `admittedFaults` to be recognized. Nothing
consulted either, so a `FaultPlan` could name a class no registry admitted and the
transition recorded it -- into `RaisedFault`, and into a `ValidMemoryEvent`'s
status, since `MemoryEvent.WellFormed` constrains counts and lengths but not fault
identity. -/
theorem an_undeclared_fault_class_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then
          .before ⟨0, h⟩ ⟨⟨"fake.neverDeclaredFault"⟩⟩ 3 3
        else .none) =
      .rejected (.faultClassNotDeclared ⟨⟨"fake.neverDeclaredFault"⟩⟩) := rfl

/-- The declared class on the same substep still runs *and is recorded*, so the
check discriminates rather than refusing every fault. Asserting only that the step
produced a state would have passed with the guard deleted and with the fault
silently dropped; review pointed that out. -/
theorem a_declared_fault_class_still_runs :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 3
        else .none)).state? = some s →
      s.faults.map RaisedFault.fault = [FaultClassId.pageFault] := by
  intro s hs
  cases hs
  decide

/-- A fault on a substep carrying an obligation ledger effect is refused, because
nothing says what becomes of the effect. Before this, a `reserve` that faulted
having written zero bytes still created its release duty, and a `release` that
faulted having written nothing still discharged one -- the second is a leak. -/
theorem a_fault_on_a_ledger_bearing_substep_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.reserve) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
        else .none) =
      .rejected .faultWithUndeclaredLedgerEffect := rfl

/-- **And a fault on a substep carrying an *authority* effect is refused too.**

The same defect in the field that arrived a milestone later, found by review after
the authority effect landed: the gate above was written for `ledgerEffect` and was
not extended, so `performAccess` applied a declared lend in full on the faulting
path. Review drove exactly this store — which writes nothing, since `writes = 0` —
to lend the buffer's head to the device engine, and drove a faulting return to
consume its identity and a faulting transfer to move a grant. -/
theorem a_fault_on_an_authority_bearing_substep_is_refused :
    Grass.Op.step policy state₀ (SomeOperation.of Alpha.lendSlot) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
        else .none) =
      .rejected .faultWithUndeclaredAuthorityEffect := rfl

/-- The same for a return and a transfer, which are the two that *lose* authority on
a path that wrote nothing. -/
theorem a_fault_on_a_returning_substep_is_refused :
    Grass.Op.step policy stateWithAuthority (SomeOperation.of Alpha.returnLoanSlot)
      thread₀ .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
        else .none) =
      .rejected .faultWithUndeclaredAuthorityEffect ∧
    Grass.Op.step policy stateWithAuthority (SomeOperation.of Alpha.handOn)
      thread₀ .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
        else .none) =
      .rejected .faultWithUndeclaredAuthorityEffect := by
  exact ⟨rfl, rfl⟩

/-- And the same operation without a fault still runs, so the rejection is the fault
path and not the effect. -/
theorem the_unfaulted_lend_still_runs :
    (stepAlpha state₀ .lendSlot).state?.isSome := by decide

/-! ## A machine that cannot fill an access is refused, not padded

`Oracle.answer` used to return a bare `Committed`, whose length obligations are
upper bounds. A profile supplying no write data for a nonempty store therefore
produced a `completed` outcome, `AccessOutcome.status` relabelled it
`partialCommit 0 0`, and the operation carried on to its later substeps having
committed nothing, with no fault and no denial. A malformed machine answer became
a successful execution, which is the shape `docs/FOUNDATION.md` law 8 names.
g-reviewer type-checked that counterexample against this fixture.

`CompleteCommitted` makes a short completion unrepresentable and the answer is an
`Option`, so an oracle that cannot fill an access says so rather than padding. -/

/-- A policy whose machine supplies no write data at all. Everything else matches
`policy`. -/
def starvedPolicy : StepPolicy :=
  { policy with oracle := .ofMemory (fun _ _ => []) indeterminateByte }

/-- **The store is refused, and refused before its later effects.**

`Alpha.reserve` writes eight bytes and creates a release obligation. Under the
starved machine nothing is written, the violation is recorded, and the obligation
is *not* created -- the operation stopped rather than reporting a successful
partial completion. -/
theorem a_machine_that_cannot_fill_a_store_is_refused :
    ∀ s, (Grass.Op.step starvedPolicy state₀ (SomeOperation.of Alpha.reserve) thread₀
        .thread ⟨⟨"alpha"⟩⟩).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.obligations.lookup releaseObligationId = Option.none ∧
      s.memory.byteAt? bufferAlloc 0 = some 0x00 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- It reports `machineAnswerIncomplete` rather than a class that would read as a
program error: the program did nothing wrong, the machine description did. -/
theorem the_starved_store_records_the_right_class :
    ∀ s, (Grass.Op.step starvedPolicy state₀ (SomeOperation.of Alpha.reserve) thread₀
        .thread ⟨⟨"alpha"⟩⟩).state? = some s →
      s.violations.records?.map AuditViolation.class_ =
        [AuditViolationClass.machineAnswerIncomplete] := by
  intro s hs
  cases hs
  decide

/-- A read is unaffected: the starved machine supplies no *write* data, and
`observedBytes` builds a full-width read from the store itself. So the check
discriminates on what is actually missing. -/
theorem the_starved_machine_still_completes_a_load :
    ∀ s, (Grass.Op.step starvedPolicy state₀ (SomeOperation.of Alpha.load) thread₀
        .thread ⟨⟨"alpha"⟩⟩).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-! ## A completed access reports that it completed

The completeness test demanded that reads *and* writes both cover the range,
unconditionally on intent. A write-only access has `readCount = 0` by
`Committed.observedAbsent`, so every ordinary load and store recorded
`partialCommit` -- whose docstring says "stopped early without faulting" -- and
`AccessStatus.IsComplete` was false for every access this model can perform except
a full-width read-modify-write.

The counts below are the second half of the same defect, found a round later: a
completed load reports `8 0` and a completed store `0 8`, where `completed`
previously carried no counts and both accessors answered "the whole range" — so a
completed load claimed to have written eight bytes. -/

theorem a_completed_load_reports_completed :
    ∀ s, (stepAlpha state₀ .load).state? = some s →
      s.events.map (·.event.status) = [AccessStatus.completed 8 0] := by
  intro s hs
  cases hs
  decide

theorem a_completed_store_reports_completed :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      s.events.map (·.event.status) = [AccessStatus.completed 0 8] := by
  intro s hs
  cases hs
  decide

/-- A genuinely partial access still reports its prefix, so the fix did not make
the status say "completed" unconditionally. The store read nothing, so its read
count is zero rather than the three the plan named -- which is the read/write
separation reaching the status, where it previously stopped at `Committed`. -/
theorem a_faulted_store_still_reports_its_prefix :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 3
          else .none)).state? = some s →
      s.events.map (·.event.status) = [AccessStatus.faulted .pageFault 0 3] := by
  intro s hs
  cases hs
  decide

/-! ## A faulting read-modify-write can keep its read without its write

`Committed` counts reads and writes separately, and `Grass/Memory/Event.lean`
motivates that with an `xadd` which observed eight bytes and then faulted before
storing. The transition truncated both lists by one shared count, so that outcome
was the one thing the fault path could not express: a faulting RMW always reported
`readCommitted = writeCommitted`. `faulted_rmw_keeps_its_read` never checked the
write, so it passed while demonstrating the opposite of its own section header. -/

theorem faulted_rmw_keeps_its_read_without_its_write :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicAdd) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 8 0
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.readCommitted = 8 ∧ e.event.writeCommitted = 0 ∧
        s.memory.byteAt? bufferAlloc 0 = some 0x00 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide, by decide⟩

/-! ## A transactional sequence exposes nothing when it faults

`FaultVisibility.transactional` says "no step is visible unless all are".
`visibleEffects?` returned `[]` for it, which handles the substeps *before* the
failure — and `runStep` then committed the faulting substep's own partial write
anyway, because nothing asked whether that one was visible. So a transactional
sequence discarded its completed substep and kept the faulting one's prefix, which
is the reverse of what it declares. Local adversarial review built the case.
`SubstepSequence.faultingEffectVisible` is the missing question. -/

/-- With the fault at the second substep, neither half is visible: not the
completed first, and not the faulting second's prefix. Both bytes still read as
the zeros the allocation started with, rather than the `0xAB` a store writes. -/
theorem transactional_exposes_nothing :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicSplitStore) thread₀
        .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 4
          else .none)).state? = some s →
      s.memory.byteAt? bufferAlloc 0 = some 0x00 ∧
      s.memory.byteAt? bufferAlloc 4 = some 0x00 ∧
      s.events = [] := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- The fault is still recorded. Nothing being *visible* is a statement about
committed effects, not about whether the machine faulted. -/
theorem transactional_still_records_its_fault :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicSplitStore) thread₀
        .thread ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 4
          else .none)).state? = some s →
      s.faults.map RaisedFault.fault = [FaultClassId.pageFault] := by
  intro s hs
  cases hs
  decide

/-! ## A reported fault cannot be discarded

An out-of-range fault index used to mean "no fault at all": `visibleEffects?` took
the whole list, the substep lookup missed, and every access committed to
completion while `step` returned `.ran`. A fault turning into a success is the
law-8 failure running in the most dangerous direction.

There is no fixture for it any more, because `FaultPlan.before` carries a
`Fin sequence.substeps.length` and the bad case is **unrepresentable**. That is
the stronger repair: a negative fixture proves a check runs, while a type that
cannot express the mistake needs no check. The `if h : _ < _` guards in the
theorems above are how a caller obtains the `Fin`, and they are discharged
statically for a known sequence. -/

/-- The store sequence has exactly one substep, so index zero is the only fault
position that exists. -/
theorem store_has_one_substep :
    ∀ seq, (HasOperationFacets.facets Alpha.store).memoryEffects = some seq →
      seq.substeps.length = 1 := by
  intro seq h
  cases h
  rfl

/-! ## 7: alias conflicts across distinct allocations -/

/--
**The stepper denies it**, not merely a lemma about `Conflicts`.

A thread stores to the buffer; a device engine then stores to the *view*, a
different allocation naming the same bytes. The second access is refused, nothing
is committed for it, and a violation is recorded.

`Provenance.SameStorage` would have called these unrelated — the allocation
identities differ, which is exactly what distinct allocations mean — so the
conflict is found only because aliasing is recorded in the machine state and the
transition consults it.
-/
theorem aliased_cross_context_store_is_denied :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWrite).state? = some t →
        t.events.length = 1 ∧ ¬ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/--
**An alias chain is followed, not just one hop.**

`state₀` declares the buffer aliased to the view and the view aliased to
`chainedAlloc`, so all three name the same bytes. `SharesBytes` compared a single
hop, so the two ends of the chain were declared non-conflicting and a
cross-context write to the far end committed with no violation — the same defect
`SharesBytes` was introduced to fix, one hop further out.
`docs/MEMORY_MODEL.md` §7.5 makes mapping and sharing typed transitions, and those
compose.
-/
theorem chained_alias_store_is_denied :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWriteChained).state? = some t →
        t.events.length = 1 ∧ ¬ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- The chain really is two hops: the buffer and `chainedAlloc` are not directly
declared aliased, so the theorem above is about transitivity and not about a
declaration that was there all along. -/
theorem the_chain_is_two_hops :
    ¬ (state₀.memory.AliasHop bufferAlloc chainedAlloc) ∧
    state₀.memory.AliasHop bufferAlloc viewAlloc ∧
    state₀.memory.AliasHop viewAlloc chainedAlloc ∧
    state₀.memory.SharesBytes bufferAlloc chainedAlloc := by decide

/-- The same two accesses, one context apart, are *not* denied: program order
sequences a context against itself, and refusing that would refuse ordinary
sequential code. -/
theorem same_context_stores_are_not_denied :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepAlpha s .storeThroughView).state? = some t →
        t.events.length = 2 ∧ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs; cases ht
  exact ⟨by decide, by decide⟩

/-- The same two stores are *not* related by `SameStorage`, so the conflict is
found only because the state records the alias. -/
theorem aliased_stores_are_not_sameStorage :
    ¬ bufferProv.SameStorage viewProv := by
  refine Provenance.not_sameStorage_of_root_ne ?_
  decide

/-! ## 8: partial effects survive a compound fault -/

/-- `divide` reads and then faults from a step that touches no memory. The read
survives, which is what `docs/MEMORY_MODEL.md` §1 requires a profile to be able to
state and what a sequence of accesses alone could not express. -/
theorem divide_preserves_its_read :
    ∀ seq, (HasOperationFacets.facets Alpha.divide).memoryEffects = some seq →
      seq.visibleEffects? 1 =
        some [acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false] := by
  intro seq h
  cases h
  rfl

/-! ## A partial read-modify-write retains its completed read

An `xadd` that observed its operand and then faulted before storing must record
the read it performed. One shared committed count made that unstateable: the
event had to claim it read as much as it wrote, so a faulted RMW with nothing
written had to claim it read nothing, while `readValuePresent` still demanded a
value. Reads and writes now count separately. -/

theorem faulted_rmw_keeps_its_read :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicAdd) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 8 8
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.kind = .readModifyWrite ∧
        e.event.readCommitted = 8 ∧ e.event.valueRead.isSome := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide, by decide⟩

/-- Truncated to three bytes, the read is three bytes and still present. The
count is the committed prefix, not the width the access named. -/
theorem partially_faulted_rmw_records_its_prefix :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.atomicAdd) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 3 3
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.readCommitted = 3 ∧ e.event.writeCommitted = 3 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide⟩

/-! ## The fault plan's commit counts are bounded by what the substep can commit

`AuditViolationClass.faultCommitOutOfRange` appeared nowhere under `Tests/`. Review
restored the pre-repair form of the bound -- the symmetric one whose asymmetry the
`faultCommitOutOfRange` docstring records finding, which refused an impossible count
on a compute substep while approximating one on an access -- and the tree stayed
green; disabling the clause outright likewise.

Nothing becomes unsound without it, because `Committed.truncate` clamps by
`List.take` and `observedAbsent` forces a write-only access's read count to zero. That
is exactly the objection: an impossible machine report is silently rewritten into a
possible one, and `docs/FOUNDATION.md` law 8 says reject rather than approximate. The
fault plan is external entropy under law 5, so the gate is where the machine's answer
is checked rather than believed. -/

/-- **A read count on an access that reads nothing is refused.** `store` writes eight
bytes and reads none, so a plan claiming one committed read byte describes something
the substep cannot have done. -/
theorem a_read_count_on_a_write_only_access_is_refused :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 1 0
        else .none)).rejection? = some .faultCommitOutOfRange := by decide

/-- The same plan with the read count zero runs, so the refusal is the count and not
the plan. -/
theorem the_same_plan_without_the_read_runs :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
        else .none)).Ran := by decide

/-- **And a non-zero count on a substep that touches no memory is refused.** This is
the half the pre-repair bound got right; it is here so that the asymmetry cannot come
back unnoticed in either direction. `divide`'s second substep is a `.compute`. -/
theorem a_commit_count_on_a_compute_substep_is_refused :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 1 < seq.substeps.length then .before ⟨1, h⟩ divideError 0 1
        else .none)).rejection? = some .faultCommitOutOfRange := by decide

/-- The same plan with both counts zero runs. -/
theorem the_same_compute_plan_without_the_count_runs :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 1 < seq.substeps.length then .before ⟨1, h⟩ divideError 0 0
        else .none)).Ran := by decide

/-! ## 9: a second family coexists -/

/-- The device family steps through the same relation, with no shared type. -/
theorem dma_runs :
    ∃ s, (stepBeta state₀ .dmaWrite).state? = some s ∧ s.violations.IsEmpty := by
  refine ⟨_, rfl, ?_⟩; decide

/-- An operation that declares no memory effects is rejected, not treated as
having none. This is `docs/FOUNDATION.md` law 8 at the seam. -/
theorem undeclared_is_rejected :
    (stepBeta state₀ .undeclared).rejection? = some (.facetsNotClosed .memoryEffects) := by
  decide

/-- **And an operation missing a facet no later branch asks about is rejected by the
closure gate itself.**

`undeclared_is_rejected` above cannot say this. It is missing `memoryEffects`, and the
branch after the gate returns `.facetsNotClosed .memoryEffects` for the same operation,
so review switched the gate off entirely -- replacing its predicate so it never
rejects -- and the whole tree stayed green. `restartability` is required by both
fixture policies and nothing downstream reads it, so this rejection can only be the
gate. -/
theorem a_missing_restartability_facet_is_rejected :
    (stepBeta state₀ .unrestartable).rejection? =
      some (.facetsNotClosed .restartability) := by decide

/-- And the gate's answer is `OperationFacets.Closes`'s answer, by
`closes_iff_no_missing`: this operation fails closure and `dmaWrite` satisfies it. -/
theorem the_closure_gate_agrees_with_closes :
    ¬ (HasOperationFacets.facets Beta.unrestartable).Closes policy.requiredFacets ∧
    (HasOperationFacets.facets Beta.dmaWrite).Closes policy.requiredFacets := by
  exact ⟨by decide, by decide⟩

/-- Both families reach the same transition relation, and neither type appears in
the other's definition. -/
theorem two_families_one_relation :
    (stepAlpha state₀ .load).Ran ∧ (stepBeta state₀ .dmaWrite).Ran := by decide

/-! ## The transition invariant

Every step extends the violation ledger. This is the property
`docs/MEMORY_MODEL.md` §8 names, and it is a fact about transitions rather than
about the ledger type, which cannot enforce it. -/

theorem every_alpha_step_extends_violations (op : Alpha) :
    ∀ s, (stepAlpha state₀ op).state? = some s →
      s.violations.Extends state₀.violations := by
  intro s hs
  cases op <;> cases hs <;>
    first
      | exact AuditViolationLedger.Extends.refl _
      | exact AuditViolationLedger.extends_append _ _
      | exact (Grass.Op.runStep_extends_violations _ _ _ _ _ _ _).trans
          (AuditViolationLedger.Extends.refl _)

/-! ## 8 again, through the transition rather than a lemma

The `divide_preserves_its_read` theorem above is a fact about the *facet*: it says
what `visibleEffects?` answers. That is not the same as saying the transition
honours it, and an earlier version of this fixture proved only the former while
the stepper committed every access unconditionally.

These drive the fault path through `step` itself. -/

/-- A compound operation that faults at its second substep. The read before it
committed, and the state shows one event. -/
theorem divide_fault_preserves_the_read :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then
            .before ⟨1, h⟩ divideError 0 0
          else .none)).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/--
Faulting at the *first* substep commits no bytes.

The event is still recorded — a faulted access is an event, and pretending
otherwise would lose it from the trace — but it committed nothing. An earlier
version of this theorem said "commits nothing" in its docstring and checked only
`events.length = 1`, which is compatible with an event that committed the whole
range.
-/
theorem divide_fault_at_zero_commits_no_bytes :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 0
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.readCommitted = 0 ∧ e.event.writeCommitted = 0 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide⟩

/-- A faulting access commits the prefix it declares, and the event records it.
`docs/MEMORY_MODEL.md` §1 forbids assuming a faulted access did nothing. -/
theorem faulted_store_commits_its_declared_prefix :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 3
          else .none)).state? = some s →
      ∃ e, s.events = [e] ∧ e.event.writeCommitted = 3 ∧ e.event.status = .faulted .pageFault 0 3 := by
  intro s hs
  cases hs
  exact ⟨_, rfl, by decide, by decide⟩

/-! ### The fault itself is recoverable from the step result

A compute substep produces no memory event, so before the state carried a fault
record a `divideError` left no trace at all: the theorems above could see that the
read survived, but nothing distinguished a faulting execution from a clean one.
That is the fault being discarded, which is what `Substep.compute` exists to
prevent. -/

/-- The divide error is present in the resulting state, with its class, its
context, and the substep it came from. -/
theorem divide_fault_is_recoverable :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.divide) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 1 < seq.substeps.length then
            .before ⟨1, h⟩ divideError 0 0
          else .none)).state? = some s →
      s.faults = [{ fault := divideError, context := thread₀, cause := ⟨⟨"alpha"⟩⟩
                    substep := 1 }] := by
  intro s hs
  cases hs
  decide

/-- A clean run of the same operation records no fault, so the two are
distinguishable. -/
theorem clean_divide_records_no_fault :
    ∀ s, (stepAlpha state₀ .divide).state? = some s → s.faults = [] := by
  intro s hs
  cases hs
  decide

/-- A fault on an *access* substep is recorded too, so the record does not depend
on which kind of substep failed. -/
theorem access_fault_is_recorded :
    ∀ s, (Grass.Op.step policy state₀ (SomeOperation.of Alpha.store) thread₀ .thread
        ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
          if h : 0 < seq.substeps.length then .before ⟨0, h⟩ .pageFault 0 3
          else .none)).state? = some s →
      s.faults.length = 1 ∧ s.events.length = 1 := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- An operation whose visibility rule belongs to a profile cannot be stepped by
the generic relation. Refusing is the honest answer; guessing which effects
survive would be the permissive fallback law 8 forbids. -/
theorem profile_visibility_rule_is_refused :
    (Grass.Op.step policy state₀ (SomeOperation.of Alpha.splitStore) thread₀ .thread
      ⟨⟨"alpha"⟩⟩ (faultAt := fun seq =>
        if h : 1 < seq.substeps.length then .before ⟨1, h⟩ .pageFault 0 0
        else .none)).rejection? = some .visibilityRuleUnknown := by decide

/-! ## The authority map, changed by an operation

Until `AuthorityDelta` existed, `Grass/Op/Step.lean` read the authority map through
`AuthorityProvider` and never wrote it, so every mutator in
`Grass/Memory/State.lean` — `issue?`, `returnGrant?`, `splitGrant?`, `joinGrants?`,
`transferGrant?` — had no caller but a fixture. A rule proved about a map the
transition does not mutate is this branch's recurring defect, found in its own layer.
These step the doors through `step`.
-/

/-- **An operation lends, and the map afterwards holds the grant.** The first
transition in this branch to change the authority map. -/
theorem the_declared_lend_lands :
    ∀ s, (stepAlpha state₀ .lendSlot).state? = some s →
      s.events.length = 1 ∧ s.violations.IsEmpty ∧
      s.memory.grantAt? lentSlot = some declaredLoan := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- And the lend takes effect *after* this access: the store commits because the map
as it stood authorized it, which is §1's every-check-against-the-pre-access-state
reading. Afterwards the same store would be refused, since the engine now holds the
bytes read-only — so this is not a state a second identical operation could reach. -/
theorem the_lending_store_is_authorized_against_the_old_map :
    ∀ s, (stepAlpha state₀ .lendSlot).state? = some s →
      s.memory.byteAt? bufferAlloc 0 = some 0xab ∧
      ¬ s.memory.Exclusive bufferProv ⟨0, 8⟩ := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide⟩

/-- **A forged lender is refused**, and the refusal is recorded rather than silent.
The program thread declared a loan whose lender is the device engine: `MayLend`
bounds what the *named* lender can lend, so this conjures nothing out of nothing;
what it would do is let one context strip another's exclusivity by lending that
other's bytes. -/
theorem the_forged_lend_is_refused :
    ∀ s, (stepAlpha state₀ .forgedLend).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.violations.records?.any (fun r => r.class_ = .authorityEffectRefused) ∧
      s.memory.grantAt? lentSlot = Option.none := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **Two lends of one identity in a single effect are refused**, because the second
is checked against the map the first left — the whole-effect check
`Grass/Obligation/Delta.lean` needed for the ledger, holding here by construction
since the applier threads the state through. -/
theorem the_repeated_lend_is_refused :
    ∀ s, (stepAlpha state₀ .lendTwice).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.memory.grantAt? lentSlot = Option.none := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- **An operation splits the loan it holds.** The source identity is consumed and
both halves are in the map, through `step`. -/
theorem the_declared_split_lands :
    ∀ s, (stepAlpha stateWithAuthority .splitLoan).state? = some s →
      s.violations.IsEmpty ∧
      s.memory.grantAt? bufferLoan = Option.none ∧
      (s.memory.grantAt? lowSlot).isSome ∧ (s.memory.grantAt? highSlot).isSome := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **And the same operation is refused when another context holds the grant.** The
map would accept the split — it is a re-description of authority either way — so this
is the actor rule in `applyAuthorityDelta?` and nothing the doors check. The grant is
untouched afterwards. -/
theorem the_non_holder_split_is_refused :
    ∀ s, (stepAlpha stateWithEngineAuthority .splitLoan).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.violations.records?.any (fun r => r.class_ = .authorityEffectRefused) ∧
      (s.memory.grantAt? bufferLoan).isSome ∧
      s.memory.grantAt? lowSlot = Option.none := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/--
**None of the authority-effect fixtures is vacuous.**

Every one of them is `∀ s, (stepAlpha … ).state? = some s → P s`, and `cases hs` on
`none = some s` closes such a goal without looking at `P`. So a *rejected* step makes
its fixture prove nothing, and this branch has made that mistake once already — a
theorem about a store presented by the wrong context, which `contextMismatch`
rejects. These are the steps those fixtures are about, asserted to run.
-/
theorem the_authority_effect_steps_run :
    (stepAlpha state₀ .lendSlot).state?.isSome ∧
    (stepAlpha state₀ .forgedLend).state?.isSome ∧
    (stepAlpha state₀ .lendTwice).state?.isSome ∧
    (stepAlpha stateWithAuthority .splitLoan).state?.isSome ∧
    (stepAlpha stateWithEngineAuthority .splitLoan).state?.isSome ∧
    (stepAlpha stateWithAuthority .returnLoanSlot).state?.isSome ∧
    (stepAlpha stateWithHalves .joinHalves).state?.isSome ∧
    (stepAlpha stateWithAuthority .handOn).state?.isSome ∧
    (stepAlpha state₀ .returnLoanSlot).state?.isSome ∧
    (stepAlpha stateWithAuthority .joinHalves).state?.isSome ∧
    (stepAlpha stateWithEngineAuthority .handOn).state?.isSome := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- **An operation returns the loan it holds**, which consumes that exact identity —
§3's rule, performed by a transition rather than by a fixture. -/
theorem the_declared_return_lands :
    ∀ s, (stepAlpha stateWithAuthority .returnLoanSlot).state? = some s →
      s.violations.IsEmpty ∧ s.memory.grantAt? bufferLoan = Option.none ∧
      (s.memory.grantAt? liveFrame).isSome := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- **And returning an identity the map does not hold is refused**, from the same
operation stepped against a state where nothing is lent. -/
theorem the_return_of_nothing_is_refused :
    ∀ s, (stepAlpha state₀ .returnLoanSlot).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      s.violations.records?.any (fun r => r.class_ = .authorityEffectRefused) := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- **An operation joins the two halves it holds.** Both sources are consumed and the
join is recorded under the identity the operation named. -/
theorem the_declared_join_lands :
    ∀ s, (stepAlpha stateWithHalves .joinHalves).state? = some s →
      s.violations.IsEmpty ∧ s.memory.grantAt? bufferLoan = Option.none ∧
      s.memory.grantAt? secondBufferLoan = Option.none ∧
      (s.memory.grantAt? lentSlot).isSome := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **And the same join is refused where the sources are not adjacent** — here
because only one of them exists, which is the unknown-source clause; the adjacency
clause itself is `Tests/Memory/Loans.lean`'s `a_gapped_join_is_refused`. -/
theorem the_join_of_one_half_is_refused :
    ∀ s, (stepAlpha stateWithAuthority .joinHalves).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      (s.memory.grantAt? bufferLoan).isSome := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- **An operation hands its loan on**, keeping the identity so the lender can still
return it — §6's return protocol surviving a transfer. -/
theorem the_declared_transfer_lands :
    ∀ s, (stepAlpha stateWithAuthority .handOn).state? = some s →
      s.violations.IsEmpty ∧
      (s.memory.grantAt? bufferLoan).any (fun grant => grant.holder = engine₀) ∧
      (s.memory.returnGrant? engine₀ bufferLoan).isSome := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- **And the same transfer is refused where the acting context does not hold the
grant.** In `stateWithEngineAuthority` the engine holds it and the thread only lent
it, so this is the only-the-holder-may-transfer rule, not the conflict rule. -/
theorem the_non_holder_transfer_is_refused :
    ∀ s, (stepAlpha stateWithEngineAuthority .handOn).state? = some s →
      s.events = [] ∧ s.violations.recordCount = 1 ∧
      (s.memory.grantAt? bufferLoan).any (fun grant => grant.holder = engine₀) := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- **A context that does not hold the sources may not join them.**

Stated on the map rather than through `step`, deliberately: the actor of an authority
effect is the descriptor's context, and a descriptor whose context is not the stepping
context is rejected by `contextMismatch` before the actor rule is reached — a fixture
on this branch was once written that way and proved the wrong thing. The triple below
is what discriminates: the door accepts the join, the actor rule refuses it, and the
holder's own join is accepted.

Review found this rule had no fixture at all. Removing it from
`applyAuthorityDelta?` left the whole build green, while its `.split` twin is caught
immediately by `the_non_holder_split_is_refused`. -/
theorem a_non_holder_may_not_join :
    stateWithHalves.memory.applyAuthorityDelta? engine₀
      (.join bufferLoan secondBufferLoan lentSlot) = Option.none ∧
    (stateWithHalves.memory.joinGrants? bufferLoan secondBufferLoan lentSlot).isSome ∧
    (stateWithHalves.memory.applyAuthorityDelta? thread₀
      (.join bufferLoan secondBufferLoan lentSlot)).isSome := by
  exact ⟨by decide, by decide, by decide⟩

/-- The same shape for `.split`, so both actor rules are pinned on the map as well as
through `step`. -/
theorem a_non_holder_may_not_split :
    stateWithAuthority.memory.applyAuthorityDelta? engine₀
      (.split bufferLoan lowSlot highSlot 32) = Option.none ∧
    (stateWithAuthority.memory.splitGrant? bufferLoan lowSlot highSlot 32).isSome ∧
    (stateWithAuthority.memory.applyAuthorityDelta? thread₀
      (.split bufferLoan lowSlot highSlot 32)).isSome := by
  exact ⟨by decide, by decide, by decide⟩

/-- **And the forged lender is refused on the map for the same reason**, which is the
half `the_forged_lend_is_refused` cannot show: through `step` the actor is fixed by
the descriptor, so only a map-level fixture can vary it. Review pointed out that the
audit guarding the doors does not guard this function, and that a caller free to
choose the actor defeats the rule — `Tools/DoorAudit.py` now covers it.
 -/
theorem the_forged_lend_is_refused_on_the_map :
    state₀.memory.applyAuthorityDelta? thread₀
      (.issue lentSlot { declaredLoan with lender := engine₀ }) = Option.none ∧
    (state₀.memory.applyAuthorityDelta? engine₀
      (.issue lentSlot { declaredLoan with lender := engine₀ })).isSome := by
  exact ⟨by decide, by decide⟩

/-! ## A race is recorded as a race

`refusalOf` recorded three different rules under `authorityUnavailable`: §3's
authority-state clause, §3's holder clause, and §7.3's conflict. Review demonstrated a
race recorded that way from a state where *nothing was held*, with a ledger entry
byte-identical in class to a genuine loan violation — so a profile could not state a
race-freedom claim separately from an authority claim, which is what §7.3's second
paragraph distinguishes. `conflictingAccess` is its own class now.
-/

/-- **The race is recorded as `conflictingAccess`, from a state where nothing is
held.** The second conjunct is the part that matters: the class cannot be explained by
any loan. -/
theorem a_race_is_recorded_as_a_race :
    ¬ state₀.memory.AnyGrantOver bufferProv ⟨0, 8⟩ ∧
    ¬ state₀.memory.AnyGrantOver viewProv ⟨0, 8⟩ ∧
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWrite).state? = some t →
        t.violations.records?.any (fun r => r.class_ = .conflictingAccess) := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hs t ht
  cases hs
  cases ht
  decide

/-- **And a race across two address spaces is a race.**

`MemoryEvent.Conflicts` carried `a.provenance.space = b.provenance.space` and a theorem
asserting the narrowing as a law of §7.5. §7.3's sentence has no address-space clause,
and §7.5's is about offset coincidence, which `SharesBytes` already implements. What
the conjunct actually did was cancel a *declared* sharing whenever the spaces differed
-- which is two of the three pairs the `SameStorage` repair was made for, a
host-visible device buffer and the allocation behind it among them.

Review stepped it: the thread wrote the buffer, the engine wrote the same declared
storage through this view, and the step committed with an empty violation ledger while
the identical store through a *cpu*-space view was refused. The authority rule had
already dropped its own space conjunct for this reason and said so, so the two rules
were answering differently about one pair of allocations. -/
theorem a_cross_space_race_is_recorded_as_a_race :
    state₀.memory.SharesBytes bufferAlloc deviceViewAlloc ∧
    deviceProv.space ≠ bufferProv.space ∧
    ¬ state₀.memory.AnyGrantOver deviceProv ⟨0, 8⟩ ∧
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWriteDeviceView).state? = some t →
        t.violations.records?.any (fun r => r.class_ = .conflictingAccess) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro s hs t ht
  cases hs
  cases ht
  decide

/-- And the same store with nothing written before it commits, so the refusal above is
the earlier write and not the device view. -/
theorem the_device_view_store_alone_commits :
    ∀ t, (stepBeta state₀ .dmaWriteDeviceView).state? = some t →
      t.events.length = 1 ∧ t.violations.IsEmpty := by
  intro t ht
  cases ht
  exact ⟨by decide, by decide⟩

/-! ## No compatibility relation can switch the race check off

`StepPolicy.compatible` is the one field a profile writes that can *remove* a refusal
rather than add one, and review used it: `compatible := fun _ _ => true` on this very
profile made every §7.3 conflict vanish, and the cross-context pair
`aliased_cross_context_store_is_denied` denies committed with an empty ledger.

§7.3's sentence exempts "compatible **atomic** accesses", and the adjective was
enforced nowhere — `MemoryEvent.Conflicts` never read `ordering.atomicity`.
`StepPolicy.compatibleIsAtomic` is what makes it load-bearing, and it is a proof field
rather than a check, so a policy that cannot discharge it cannot be constructed.
-/

/-- A profile that declares every pair compatible. It type-checks only because the
two accesses it would exempt are both atomic; the fixture's own operations are not,
which is the point of the theorem below. -/
def permissiveCompatible (a b : MemoryEvent) : Bool :=
  decide (a.ordering.atomicity = .atomic) && decide (b.ordering.atomicity = .atomic)

/-- The permissive policy is constructible, so the theorem below is not about a
vacuous premise: a profile may exempt every *atomic* pair, which is exactly what
§7.3 allows. -/
def permissivePolicy : StepPolicy :=
  { policy with
    compatible := permissiveCompatible
    compatibleIsAtomic := by
      intro a b h
      simp only [permissiveCompatible, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h
    compatibleSymm := by
      intro a b h
      simp only [permissiveCompatible, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨h.2, h.1⟩ }

/-- **And the race is still refused under it.** The thread's store and the engine's
write to the same bytes are non-atomic, so no compatibility relation a profile can
write exempts them — `compatibleIsAtomic` is what closes that. -/
theorem the_permissive_policy_still_denies_the_race :
    ∀ s, (Grass.Op.step permissivePolicy state₀ (SomeOperation.of Alpha.store) thread₀
        .thread ⟨⟨"alpha"⟩⟩).state? = some s →
      ∀ t, (Grass.Op.step permissivePolicy s (SomeOperation.of Beta.dmaWrite) engine₀
          .dmaEngine ⟨⟨"beta"⟩⟩).state? = some t →
        t.events.length = 1 ∧ ¬ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs
  cases ht
  exact ⟨by decide, by decide⟩

/-- And the same pair under the default policy, so the theorem above is the
compatibility relation and not something else about the permissive profile. -/
theorem the_default_policy_denies_the_race :
    ∀ s, (stepAlpha state₀ .store).state? = some s →
      ∀ t, (stepBeta s .dmaWrite).state? = some t →
        t.events.length = 1 ∧ ¬ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs
  cases ht
  exact ⟨by decide, by decide⟩

/-! ## An obligation identity is reused after its duty ends

`LedgerDelta.Applicable`'s create clause is `o.id ∉ live` — "not currently live",
not "never issued" — and there is no obligation supply on `MachineState` to make the
stronger reading available. An earlier version of `Grass/Obligation/Delta.lean` said
outputs are fresh because "identities come from a supply that never reissues"; review
stepped the three operations below and got the same identity carrying a second duty.

Latent, because `TerminalOutcome` is keyed by identity and terminal accounting is
M5's. It is here so that the gap is visible in compiled code, and so that adding a
supply breaks this theorem rather than passing unnoticed.
-/

/-- **reserve, release, reserve gives one identity two duties.** -/
theorem an_obligation_identity_is_reissued :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .release).state? = some t →
        ∀ u, (stepAlpha t .reserve).state? = some u →
          s.obligations.lookup releaseObligationId = some releaseObligation ∧
          t.obligations.lookup releaseObligationId = Option.none ∧
          u.obligations.lookup releaseObligationId = some releaseObligation := by
  intro s hs t ht u hu
  cases hs
  cases ht
  cases hu
  exact ⟨by decide, by decide, by decide⟩

/-! ## A duty may not be handed to a context that does not exist

`LedgerDelta.Applicable`'s transfer clause checked liveness, protocol and the actor's
ownership, and said nothing about `newOwner` — so a duty could be handed to an
identity no context ever had, after which nothing could ever discharge it, because
discharge requires the actor to own it. `docs/OBLIGATIONS.md` §3's terminal
disposition is then false of that ledger under every execution: a way to strand a
duty permanently rather than a way to drop one. §4.4.1 recorded the gap and named
`MachineState.contexts` as the set to check against.

**What the machine knows is what has executed.** `contexts` is populated by
`noteContext`, so a context that has never stepped is not a destination. That is the
conservative reading and it has a cost: handing a duty to a thread before it runs is
refused. `docs/FOUNDATION.md` law 8 prefers the refusal to a permissive default, and
a profile that needs the other behaviour has to say so.
-/

/-- The thread reserves, then hands its duty to a context the machine has never
seen. **Refused**, and the duty survives. -/
theorem a_duty_may_not_be_handed_to_a_stranger :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepAlpha s .handDutyToAStranger).state? = some t →
        (t.obligations.lookup releaseObligationId).map Obligation.owner = some thread₀ ∧
        ¬ t.violations.IsEmpty := by
  intro s hs t ht
  cases hs
  cases ht
  exact ⟨by decide, by decide⟩

/-- **And to a context it has seen, it goes through**, so the refusal is the
destination rule and not a ban on transfer. The engine has stepped by then. -/
theorem a_duty_may_be_handed_to_a_known_context :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      ∀ t, (stepBeta s .dmaWrite).state? = some t →
        ∀ u, (stepAlpha t .handDutyToTheEngine).state? = some u →
          (u.obligations.lookup releaseObligationId).map Obligation.owner = some engine₀ ∧
          u.violations.recordCount = t.violations.recordCount := by
  intro s hs t ht u hu
  cases hs
  cases ht
  cases hu
  exact ⟨by decide, by decide⟩

/-- A vocabulary that lists one name as both an atomicity justification and a
fault-visibility rule. Well typed, and refused. -/
def confusedVocabulary : AdmittedVocabulary :=
  { vocabulary with
    atomicityJustifications := ⟨[⟨"fake.splitStore"⟩]⟩ }

/-- **A vocabulary that conflates two claims under one name is not well formed**, so
no `StepPolicy` can carry it.

The three justification registries are separate precisely so that one name cannot
satisfy another's claim — a rule permitting an uninitialized read is not a proof that
a two-substep store is all-or-nothing. Review pointed out that nothing stopped a
vocabulary listing one name in two of them, which re-created at the profile level the
collapse the split was built to prevent: the split was a convention rather than a
guarantee. `AdmittedVocabulary.WellFormed` requires the three to be pairwise disjoint
now, and `StepPolicy.vocabularyWellFormed` makes that a construction obligation. -/
theorem a_confused_vocabulary_is_not_well_formed :
    ¬ confusedVocabulary.WellFormed ∧ vocabulary.WellFormed := by
  exact ⟨by decide, by decide⟩

/-- The same confusion between initialization and atomicity. -/
def confusedInitAtomicity : AdmittedVocabulary :=
  { vocabulary with
    atomicityJustifications := ⟨[⟨"fake.zeroedByLoader"⟩]⟩ }

/-- And between initialization and fault visibility. -/
def confusedInitVisibility : AdmittedVocabulary :=
  { vocabulary with
    faultVisibilityRules := ⟨[⟨"fake.zeroedByLoader"⟩]⟩ }

/-- **The other two pairs are refused too.** Disjointness is three conditions and only
the atomicity/fault-visibility pair had a fixture: review replaced each of the other
two with `True` and the tree stayed green. A rule that permits an uninitialized read is
not a proof that a two-substep store is all-or-nothing, and it is not a fault-visibility
rule either; the registries are separate so that one name cannot answer another's
question, and two thirds of that was a convention rather than a guarantee. -/
theorem the_other_two_confusions_are_refused :
    ¬ confusedInitAtomicity.WellFormed ∧ ¬ confusedInitVisibility.WellFormed := by
  exact ⟨by decide, by decide⟩

/-- **A protocol the profile never declared is not admitted.**

The clause that makes `ProtocolAuthority` mean something. Its type index stops
authority for one protocol being presented for another, and stopped nothing else:
`mintedBy` is public and total, so review minted authority for a protocol out of a
string in a foreign module and used it to discharge a duty this family had created
under `bufferProtocol` — duty gone, ledger clean, no violation. The rejection is
`accessNotAdmitted`, before applicability is asked, which is where every other
undeclared open name is caught. -/
theorem a_forged_protocol_is_refused :
    (stepAlpha state₀ .forgedProtocolRelease).rejection? =
      some (.accessNotAdmitted (.protocolNotRecognized forgedProtocol)) := by decide

/-- And the same discharge under the protocol the profile *does* declare runs, so the
rejection is the registry and not the discharge. The duty has to exist first. -/
theorem the_declared_protocol_is_admitted :
    ∀ s, (stepAlpha state₀ .reserve).state? = some s →
      (stepAlpha s .release).state?.isSome ∧
      vocabulary.protocols.Recognizes bufferProtocol ∧
      ¬ vocabulary.protocols.Recognizes forgedProtocol := by
  intro s hs
  cases hs
  exact ⟨by decide, by decide, by decide⟩

/-- **A grant kind the profile never declared is not admitted.**

`GrantKind` was an open nominal name with no registry, which did not matter while
only a fixture could mint a grant: nothing an operation carried could. Now that
`AccessDescriptor.authorityEffect` exists, an operation can, and
`MemoryState.AnyGrantOver` is kind-blind — every rule that asks whether anything is
held over some bytes counts a grant of any kind — so an invented kind would freeze
bytes while no provider's `GrantedOfKind` could ever match it.

The rejection is `accessNotAdmitted`, before any question of whether the map would
accept the lend, which is where every other undeclared open name is caught. -/
theorem an_invented_grant_kind_is_refused :
    (stepAlpha state₀ .lendInventedKind).rejection? =
      some (.accessNotAdmitted (.grantKindNotRecognized inventedKind)) := by decide

/-- And the same operation with the declared kind runs, so the rejection is the
registry and not the lend. -/
theorem the_declared_kind_is_admitted :
    (stepAlpha state₀ .lendSlot).state?.isSome ∧
    vocabulary.grantKinds.Recognizes GrantKind.loan ∧
    ¬ vocabulary.grantKinds.Recognizes inventedKind := by
  exact ⟨by decide, by decide, by decide⟩

end Grass.Tests.FakeIsa

