/-!
# Fixed-width little-endian integers over `List UInt8`

Artifact formats instantiate `Grass.Target.Format`, whose `write`/`read`
operate directly on `List UInt8` (`Grass/Target/Artifact.lean`). This module
gives every native artifact format (flat boot images, ELF, PE) one shared,
unconditionally round-tripping little-endian encoder/decoder, so each format
states its own header layout without reproving base-256 digit arithmetic.

`natToLE width n` emits the `width` least-significant base-256 digits of `n`,
least-significant byte first; `readLE width` recovers exactly `n % 256 ^
width` from the head of a byte list. The two compose to an *unconditional*
round trip (no bound hypothesis on `n`): callers who want to recover `n`
itself use `Nat.mod_eq_of_lt` once they know `n < 256 ^ width`, which is
exactly what the fixed-width host integer types (`UInt8`, `UInt16`, `UInt32`,
`UInt64`) already guarantee for their own bit width, so the derived
`writeUXX`/`readUXX` pairs below round-trip unconditionally too.
-/

namespace Grass.Artifact.Binary

/-- Little-endian digits of `n` in base 256, truncated to exactly `width`
bytes (least significant first). -/
def natToLE : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: natToLE w (n / 256)

@[simp] theorem length_natToLE (w n : Nat) : (natToLE w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [natToLE, ih]

/-- Decode a little-endian natural of exactly `width` bytes from the head of
the list; `none` if the list is too short. -/
def readLE : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bytes => some (0, bytes)
  | _ + 1, [] => none
  | w + 1, b :: bytes =>
      match readLE w bytes with
      | none => none
      | some (n, rest) => some (b.toNat + 256 * n, rest)

/-- The unconditional round trip: decoding the encoding of `n` recovers
exactly `n % 256 ^ width`, whatever `n` and the trailing bytes are. -/
theorem readLE_natToLE_append (w n : Nat) (rest : List UInt8) :
    readLE w (natToLE w n ++ rest) = some (n % 256 ^ w, rest) := by
  induction w generalizing n with
  | zero => simp [natToLE, readLE, Nat.mod_one]
  | succ w ih =>
      simp only [natToLE, List.cons_append, readLE]
      rw [ih (n / 256)]
      have hb : (UInt8.ofNat (n % 256)).toNat = n % 256 := by simp
      have step : n % 256 ^ (w + 1) = n % 256 + 256 * (n / 256 % 256 ^ w) := by
        have hpow : (256 : Nat) ^ (w + 1) = 256 * 256 ^ w := Nat.pow_succ'
        rw [hpow]
        exact Nat.mod_mul
      simp [hb, step]

/-- The width-`n` encoding of the value the reader recovers, when `n` already
fits: the ordinary round trip stated as an equality on `n` itself. -/
theorem readLE_natToLE_append_of_lt {w n : Nat} (bound : n < 256 ^ w)
    (rest : List UInt8) : readLE w (natToLE w n ++ rest) = some (n, rest) := by
  rw [readLE_natToLE_append, Nat.mod_eq_of_lt bound]

/-- Consume exactly `count` bytes from the head of the list, or `none` if the
list is too short. -/
def takeBytes : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, bytes => some ([], bytes)
  | _ + 1, [] => none
  | n + 1, b :: bytes =>
      match takeBytes n bytes with
      | none => none
      | some (taken, rest) => some (b :: taken, rest)

/-- Reading back exactly a chunk's own length recovers it and the exact
suffix, whatever the trailing bytes are. -/
theorem takeBytes_append (xs rest : List UInt8) :
    takeBytes xs.length (xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => simp [takeBytes]
  | cons x xs ih => simp [takeBytes, ih]

/-- The general form used when the count is supplied as an equal but
differently-spelled expression (e.g. a header field defined to be the
length). -/
theorem takeBytes_append_of_eq {xs rest : List UInt8} {n : Nat}
    (lengthEq : xs.length = n) : takeBytes n (xs ++ rest) = some (xs, rest) := by
  rw [← lengthEq]; exact takeBytes_append xs rest

/-! ## Native fixed-width host integers

`UInt8.toNat`/`UInt16.toNat`/`UInt32.toNat`/`UInt64.toNat` are already bounded
below their type's bit width, so encoding through `Nat` and decoding back
never truncates: these pairs round-trip unconditionally. -/

/-- Little-endian bytes of a 16-bit host integer. -/
def writeU16LE (v : UInt16) : List UInt8 := natToLE 2 v.toNat

/-- Decode a 16-bit little-endian host integer from the head of the list. -/
def readU16LE (bytes : List UInt8) : Option (UInt16 × List UInt8) :=
  match readLE 2 bytes with
  | none => none
  | some (n, rest) => some (UInt16.ofNat n, rest)

theorem readU16LE_writeU16LE_append (v : UInt16) (rest : List UInt8) :
    readU16LE (writeU16LE v ++ rest) = some (v, rest) := by
  have bound : v.toNat < 256 ^ 2 := by
    have := v.toNat_lt_size
    simpa [UInt16.size] using this
  simp [writeU16LE, readU16LE, readLE_natToLE_append_of_lt bound]

/-- Little-endian bytes of a 32-bit host integer. -/
def writeU32LE (v : UInt32) : List UInt8 := natToLE 4 v.toNat

/-- Decode a 32-bit little-endian host integer from the head of the list. -/
def readU32LE (bytes : List UInt8) : Option (UInt32 × List UInt8) :=
  match readLE 4 bytes with
  | none => none
  | some (n, rest) => some (UInt32.ofNat n, rest)

theorem readU32LE_writeU32LE_append (v : UInt32) (rest : List UInt8) :
    readU32LE (writeU32LE v ++ rest) = some (v, rest) := by
  have bound : v.toNat < 256 ^ 4 := by
    have := v.toNat_lt_size
    simpa [UInt32.size] using this
  simp [writeU32LE, readU32LE, readLE_natToLE_append_of_lt bound]

/-- Little-endian bytes of a 64-bit host integer. -/
def writeU64LE (v : UInt64) : List UInt8 := natToLE 8 v.toNat

/-- Decode a 64-bit little-endian host integer from the head of the list. -/
def readU64LE (bytes : List UInt8) : Option (UInt64 × List UInt8) :=
  match readLE 8 bytes with
  | none => none
  | some (n, rest) => some (UInt64.ofNat n, rest)

theorem readU64LE_writeU64LE_append (v : UInt64) (rest : List UInt8) :
    readU64LE (writeU64LE v ++ rest) = some (v, rest) := by
  have bound : v.toNat < 256 ^ 8 := by
    have := v.toNat_lt_size
    simpa [UInt64.size] using this
  simp [writeU64LE, readU64LE, readLE_natToLE_append_of_lt bound]

@[simp] theorem length_writeU16LE (v : UInt16) : (writeU16LE v).length = 2 := by
  simp [writeU16LE]

@[simp] theorem length_writeU32LE (v : UInt32) : (writeU32LE v).length = 4 := by
  simp [writeU32LE]

@[simp] theorem length_writeU64LE (v : UInt64) : (writeU64LE v).length = 8 := by
  simp [writeU64LE]

/-! ## Consuming (without decoding) a fixed-width field

`takeBytes_append`'s count is spelled `xs.length`, so a goal that instead
spells the count as the field's own literal width (`2`, `4`, `8` — the shape
every header field that is written but not decoded back takes) does not
syntactically match it for `simp`/`rw`. These three corollaries restate the
same fact at each literal width so a header reader that skips a field with
plain `takeBytes 4 ...` still gets a one-step rewrite. -/

theorem takeBytes_writeU16LE_append (v : UInt16) (rest : List UInt8) :
    takeBytes 2 (writeU16LE v ++ rest) = some (writeU16LE v, rest) :=
  takeBytes_append_of_eq (length_writeU16LE v)

theorem takeBytes_writeU32LE_append (v : UInt32) (rest : List UInt8) :
    takeBytes 4 (writeU32LE v ++ rest) = some (writeU32LE v, rest) :=
  takeBytes_append_of_eq (length_writeU32LE v)

theorem takeBytes_writeU64LE_append (v : UInt64) (rest : List UInt8) :
    takeBytes 8 (writeU64LE v ++ rest) = some (writeU64LE v, rest) :=
  takeBytes_append_of_eq (length_writeU64LE v)

end Grass.Artifact.Binary
