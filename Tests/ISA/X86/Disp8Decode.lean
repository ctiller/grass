import Grass.ISA.X86.Decode

/-!
# The one-byte displacement, which only the decoder reaches

`Grass.ISA.X86.encodeMem` is a canonical encoder rather than a minimal one:
every memory form it builds carries `mod=10` and a `disp32`, and no shorter
displacement is ever chosen. `Grass/ABI/Win64/UnwindBytes.lean` records what
that costs when matching an assembler.

It has a second consequence, which a sweep found. `dispKindFor`'s `mod=01` arm
is unreachable from anything this library emits, so it is exercised only when
*reading* bytes somebody else wrote -- and nothing did. Changing that arm to
answer `.d32` left the whole repository green, while a decoder given
`48 8B 45 08` would try to read four displacement bytes where one follows,
run off the end of the instruction and resume inside the next.

`Tools/x86-ndisasm-differential.py` would catch it. That needs `ndisasm`, which
a Windows build host does not have, so the arm had no check that runs
everywhere. These are that check.
-/

namespace Tests.ISA.X86.Disp8Decode

open Grass.ISA.X86

/-! ## The rule itself, at all four `mod` values -/

example : dispKindFor ModRm.modDisp8 5 none = .d8 := rfl
example : dispKindFor ModRm.modDisp32 5 none = .d32 := rfl
example : dispKindFor ModRm.modRegisterDirect 5 none = .none := rfl

/-- `mod=00` is the interesting one: no displacement in general, but `rm=101`
is RIP-relative and carries a `disp32`. -/
example : dispKindFor ModRm.modNoDisplacement 0 none = .none := rfl
example : dispKindFor ModRm.modNoDisplacement ModRm.rmSelectsRipRelative none
    = .d32 := rfl

/-! ## A real instruction

`48 8B 45 08` is `mov rax, [rbp+8]`: `REX.W`, opcode `8B`, a `ModR/M` byte of
`mod=01, reg=000, rm=101`, and one displacement byte. Four bytes total. -/

/-- It decodes, and the displacement is the one byte that followed. -/
example : ((decodeInsn [0x48, 0x8B, 0x45, 0x08]).toOption.map
    (fun p => p.1.disp)) = some (.d8 0x08) := rfl

/-- And it consumes exactly four bytes, leaving the `90` after it unread. This
is the half that fails if `mod=01` claims a `disp32`: the length is what a
decoder gets wrong, and a wrong length corrupts every instruction after it
rather than only this one. -/
example : (decodeInsn [0x48, 0x8B, 0x45, 0x08, 0x90]).toOption.map
    (fun p => p.2) = some [0x90] := rfl

/-- The same access written with a `disp32` -- `mod=10`, `ModR/M` byte `85` --
is seven bytes for the same effect. Both are legal encodings of one
instruction, which is why the `mod` field and not the operand decides the
length. -/
example : (decodeInsn [0x48, 0x8B, 0x85, 0x08, 0x00, 0x00, 0x00, 0x90]).toOption.map
    (fun p => p.2) = some [0x90] := rfl

/-- What this library would emit for that access: the `disp32` form. The two
examples above are both decodable, and only the second is something
`encodeMem` produces. -/
example : (leaR64 .rax (.base .rbp 8)).map InsnEncoding.disp
    = some (.d32 8) := rfl

end Tests.ISA.X86.Disp8Decode
