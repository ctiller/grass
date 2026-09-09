import Grass.ISA.X86.Decode

/-! Checked canonical decoding and fallthrough-PC arithmetic over observed bytes.
This leaf does not claim that the bytes were fetched from memory. A fetched-site
adapter must supply the actual checked execute-access observation at this RIP,
and the source adapter must tie it to the emitted artifact. -/
namespace Grass.ISA.X86.Execution

open Grass.Std.Logical

/-- Decoder evidence at a specified PC, with canonical bytes and a nonwrapping
fallthrough PC. The input byte sequence is an observation, not another memory store.
This cursor is not a control-flow instruction's architectural next RIP. -/
structure DecodedSite (rip : BitVec 64) (bytes : ByteSeq) where
  private mk ::
  encoding : InsnEncoding
  rest : ByteSeq
  decoded : decodeInsn bytes = .ok (encoding, rest)
  bytesExact : bytes = encoding.toBytes ++ rest
  lengthBound : 0 < encoding.size ∧ encoding.size ≤ 15
  fallthroughFits : rip.toNat + encoding.size < 2 ^ 64

namespace DecodedSite

/-- A malformed or unsupported observation never produces a decoded-site proof. -/
inductive Error where
  | decode (error : DecodeError)
  | nonCanonical
  | instructionLength
  | fallthroughWrap
deriving DecidableEq, Repr

/-- The accepted encoding is obtained from the existing decoder, not supplied
by the caller. Exact source membership remains a separate adapter obligation. -/
def check (rip : BitVec 64) (bytes : ByteSeq) : Except Error (DecodedSite rip bytes) :=
  match hd : decodeInsn bytes with
  | .error error => .error (.decode error)
  | .ok (encoding, rest) =>
      if hb : bytes = encoding.toBytes ++ rest then
        if hl : 0 < encoding.size ∧ encoding.size ≤ 15 then
          if hn : rip.toNat + encoding.size < 2 ^ 64 then
            .ok ⟨encoding, rest, hd, hb, hl, hn⟩
          else .error .fallthroughWrap
        else .error .instructionLength
      else .error .nonCanonical

def fallthroughRip {rip : BitVec 64} {bytes : ByteSeq} (site : DecodedSite rip bytes) :
    BitVec 64 := BitVec.ofNat 64 (rip.toNat + site.encoding.size)

theorem fallthroughRip_toNat {rip : BitVec 64} {bytes : ByteSeq}
    (site : DecodedSite rip bytes) :
    site.fallthroughRip.toNat = rip.toNat + site.encoding.size := by
  simp only [fallthroughRip, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt site.fallthroughFits

theorem fallthroughRip_advanced {rip : BitVec 64} {bytes : ByteSeq}
    (site : DecodedSite rip bytes) : rip.toNat < site.fallthroughRip.toNat := by
  rw [site.fallthroughRip_toNat]
  exact Nat.lt_add_of_pos_right site.lengthBound.1

theorem observed_prefix {rip : BitVec 64} {bytes : ByteSeq}
    (site : DecodedSite rip bytes) : bytes.take site.encoding.size = site.encoding.toBytes := by
  calc
    bytes.take site.encoding.size =
        (site.encoding.toBytes ++ site.rest).take site.encoding.size :=
      congrArg (List.take site.encoding.size) site.bytesExact
    _ = site.encoding.toBytes := by rw [← site.encoding.length_toBytes]; simp

theorem observed_suffix {rip : BitVec 64} {bytes : ByteSeq}
    (site : DecodedSite rip bytes) : bytes.drop site.encoding.size = site.rest := by
  calc
    bytes.drop site.encoding.size =
        (site.encoding.toBytes ++ site.rest).drop site.encoding.size :=
      congrArg (List.drop site.encoding.size) site.bytesExact
    _ = site.rest := by rw [← site.encoding.length_toBytes]; simp

/-- `encoding_unique` identifies the decoded encoding for the same observed byte stream. -/
theorem encoding_unique {rip : BitVec 64} {bytes : ByteSeq}
    (a b : DecodedSite rip bytes) : a.encoding = b.encoding := by
  have h := a.decoded.symm.trans b.decoded
  exact congrArg Prod.fst (Except.ok.inj h)

end DecodedSite
end Grass.ISA.X86.Execution
