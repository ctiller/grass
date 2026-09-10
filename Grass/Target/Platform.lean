import Grass.Target.ISA

/-!
# The platform seam

A `Platform isa D` gives meaning to an ISA's native calls in the portable
service vocabulary `D`, supplies the entry context, and owns the environment:
what the program was started with, which responses the outside world may give,
and how the environment changes when it gives them.

The platform does not execute instructions and does not know any program. It
knows its ABI (which registers carry arguments, how results come back), its
call convention (imports, syscall numbers, host function indices), and the
external semantics of the requests it can realize (a console write may be
partial; a read returns the next bytes of stdin; exit never returns).

`Responds` is relational: partial writes, failures and scheduling are choices
of the environment, not of the program. A platform that only ever answers with
success is lying and its adequacy theorems are worthless; a platform whose
`Responds` is empty for some reachable request makes the machine stuck, which
is the correct refusal.
-/

namespace Grass.Target

open Grass.Service

/-- A platform realizing the service domain `D` for the ISA `isa`. -/
structure Platform (isa : ISA) (D : Domain) where
  /-- Everything outside the program: arguments, stdin, console availability,
  clock, heap capacity, sockets, display. -/
  Environment : Type
  /-- The environments this platform is willing to start a program in. -/
  Admits : Environment → Prop
  /-- What the loader hands the machine at entry. -/
  entry : Environment → isa.InitialContext
  /-- Decode a native call into a portable request. `none` means the call is
  not one this platform realizes, which leaves the machine stuck. -/
  decode : isa.NativeCall → Option D.Request
  /-- The responses the environment may give to a request, and the environment
  after giving it. -/
  Responds : Environment → (request : D.Request) → D.Response request → Environment → Prop
  /-- Encode a response as the ISA-level effect of returning from the call. -/
  encodeReturn : (call : isa.NativeCall) → (request : D.Request) → D.Response request →
    isa.NativeReturn

end Grass.Target
