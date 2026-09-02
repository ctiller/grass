import Grass.Core.Uid
import Grass.Core.Name

/-!
# Execution contexts

The identity and kind of an execution context: the agent that performs an access,
holds an obligation, or contributes events to a consistency graph.

`docs/MEMORY_MODEL.md` §7.1 lists thread, interrupt or exception handler, signal
or callback, device queue, shader invocation, DMA engine, loader, and external
API agent, and adds that "profiles may add fields but may not reinterpret common
ones". The kind is therefore an open nominal name and the identity is generative.

Contexts are minted from a `FreshSupply` like every other identity, which is what
keeps a retired thread's numeric slot from being reused by a new thread that then
inherits the old one's authority (`docs/FOUNDATION.md` law 22).

**Custody note.** `Grass.Core` is not owned by the memory agent. This module is
temporary custody under `docs/MEMORY_IMPLEMENTATION_PLAN.md` §2. It lives in
`Core` rather than `Memory` because `Grass.Obligation` needs a context to name an
obligation's owner and must not import `Grass.Memory`. The eventual owner may
well be `Semantics`; the transfer is a rename and re-export.
-/

namespace Grass.Core

/-- Phantom tag for execution-context identities. -/
inductive ContextTag : Type

/-- The generative identity of one execution context. -/
abbrev ContextId := Uid ContextTag

/--
What kind of agent an execution context is.

Open nominal: a device or platform profile introduces its own kind rather than
editing this module. The kinds defined here are those `docs/MEMORY_MODEL.md`
§7.1 enumerates.
-/
structure ContextKind where
  /-- The kind's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace ContextKind

/-- An ordinary thread of execution. -/
def thread : ContextKind := ⟨⟨"thread"⟩⟩

/-- An interrupt or exception handler. -/
def interruptHandler : ContextKind := ⟨⟨"interruptHandler"⟩⟩

/-- A signal handler or asynchronous callback. -/
def signalHandler : ContextKind := ⟨⟨"signalHandler"⟩⟩

/-- A device command queue. -/
def deviceQueue : ContextKind := ⟨⟨"deviceQueue"⟩⟩

/-- One shader invocation. -/
def shaderInvocation : ContextKind := ⟨⟨"shaderInvocation"⟩⟩

/-- A DMA engine acting independently of the CPU. -/
def dmaEngine : ContextKind := ⟨⟨"dmaEngine"⟩⟩

/-- The image loader, acting before entry. -/
def loader : ContextKind := ⟨⟨"loader"⟩⟩

/-- An external API agent acting on the program's behalf. -/
def externalAgent : ContextKind := ⟨⟨"externalAgent"⟩⟩

end ContextKind

/-- An execution context: its identity together with what kind of agent it is. -/
structure ExecutionContext where
  /-- The context's generative identity. -/
  id : ContextId
  /-- What kind of agent it is. -/
  kind : ContextKind
deriving DecidableEq, Repr

end Grass.Core
