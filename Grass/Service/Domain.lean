/-!
# Portable service vocabulary

A `Service.Domain` is the platform-independent vocabulary of external
requests a program can make and the responses it can receive. Everything
above the platform tier (portable specifications, drivers, the generic machine
semantics) speaks only this vocabulary. Every platform (Win32, Linux, WASI,
bare metal) maps its own native call convention onto a domain; every ISA
(x86-64, AArch64, Wasm) exposes native calls without knowing which domain they
will be interpreted in.

No domain, ISA, or platform is allowed to mention a particular program.

`Event` is the audit-event type of the generic machine tier. `silent` is a CPU
step with no externally visible effect; the observation projection of every
specification-authoring facade drops it.
-/

namespace Grass.Service

/-- A vocabulary of external requests and their typed responses. -/
structure Domain where
  Request : Type
  Response : Request → Type
  /-- A terminal request ends the program; no response is delivered. -/
  Terminal : Request → Prop

/-- Audit events of a program running against a domain. -/
inductive Event (D : Domain) : Type
  | silent
  | call (request : D.Request)
  | reply (request : D.Request) (response : D.Response request)

/-- Disjoint union of two domains. A program uses one composite domain
assembled from the families it actually needs. -/
def Domain.sum (A B : Domain) : Domain where
  Request := A.Request ⊕ B.Request
  Response
    | .inl r => A.Response r
    | .inr r => B.Response r
  Terminal
    | .inl r => A.Terminal r
    | .inr r => B.Terminal r

/-- The observable (non-silent) events of a trace. -/
def Event.observable {D : Domain} : List (Event D) → List (Event D)
  | [] => []
  | .silent :: rest => observable rest
  | event :: rest => event :: observable rest

@[simp] theorem Event.observable_nil {D : Domain} :
    Event.observable ([] : List (Event D)) = [] := rfl

@[simp] theorem Event.observable_silent {D : Domain} (rest : List (Event D)) :
    Event.observable (.silent :: rest) = Event.observable rest := rfl

@[simp] theorem Event.observable_call {D : Domain} (r : D.Request) (rest : List (Event D)) :
    Event.observable (.call r :: rest) = .call r :: Event.observable rest := rfl

@[simp] theorem Event.observable_reply {D : Domain} (r : D.Request) (ρ : D.Response r)
    (rest : List (Event D)) :
    Event.observable (.reply r ρ :: rest) = .reply r ρ :: Event.observable rest := rfl

theorem Event.observable_append {D : Domain} (left right : List (Event D)) :
    Event.observable (left ++ right) = Event.observable left ++ Event.observable right := by
  induction left with
  | nil => rfl
  | cons head rest ih =>
      cases head <;> simp [ih]

/-! ## Standard domains

These are the portable families the spikes need. A platform realizes only the
families a program's plan selects. Adding a family here is a reviewed change:
it extends what every platform must be able to mean, not what one program does.
-/

/-- Byte streams of a hosted process. -/
inductive Stream where
  | stdin
  | stdout
  | stderr
  deriving DecidableEq, Repr

/-! Console I/O and process exit. -/
namespace Console

inductive Request where
  /-- Write bytes to a stream. The response is the number of bytes accepted,
  which may be less than offered (partial write) or an error. -/
  | write (stream : Stream) (bytes : List UInt8)
  /-- Read up to `max` bytes. The response is the bytes delivered; the empty
  list is end of stream. -/
  | read (stream : Stream) (max : Nat)
  /-- Whether the stream is available at all (a detached console, a closed
  descriptor). -/
  | query (stream : Stream)
  /-- Terminate the process with a status. Terminal. -/
  | exit (status : UInt32)

inductive WriteResponse where
  | accepted (count : Nat)
  | failed

inductive ReadResponse where
  | delivered (bytes : List UInt8)
  | failed

def Response : Request → Type
  | .write .. => WriteResponse
  | .read .. => ReadResponse
  | .query _ => Bool
  | .exit _ => Empty

def domain : Domain where
  Request := Request
  Response := Response
  Terminal
    | .exit _ => True
    | _ => False

end Console

/-! Dynamic memory from the host. Addresses are opaque handles; the machine
tier maps them to its own address space through the platform. -/
namespace Heap

inductive Request where
  | allocate (bytes : Nat)
  | reallocate (handle : Nat) (bytes : Nat)
  | release (handle : Nat)

def Response : Request → Type
  | .allocate _ => Option Nat
  | .reallocate .. => Option Nat
  | .release _ => Bool

def domain : Domain where
  Request := Request
  Response := Response
  Terminal := fun _ => False

end Heap

/-! Monotonic time. -/
namespace Clock

inductive Request where
  | now

def Response : Request → Type
  | .now => Nat

def domain : Domain where
  Request := Request
  Response := Response
  Terminal := fun _ => False

end Clock

end Grass.Service
