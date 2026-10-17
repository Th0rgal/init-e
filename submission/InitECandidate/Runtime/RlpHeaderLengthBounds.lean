import InitECandidate.Runtime.RlpReadLengthCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The source subtraction defining a long header's length-of-length stays
between one and eight, with no modular subtraction wrap. -/
theorem rlp_header_length_bytes (header base : BitVec 64)
    (lower : base.toNat < header.toNat) (upper : header.toNat ≤ base.toNat + 8) :
    1 ≤ (header - base).toNat ∧ (header - base).toNat ≤ 8 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
  omega

theorem rlp_long_string_length_bytes (header : BitVec 64)
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191) :
    1 ≤ (header - 183).toNat ∧ (header - 183).toNat ≤ 8 := by
  exact rlp_header_length_bytes header 183 lower upper

/-- A loaded byte supplies the upper endpoint for the final long-list case. -/
theorem rlp_long_list_length_bytes (byte : UInt8)
    (lower : 247 < (BitVec.ofNat 64 byte.toNat).toNat) :
    1 ≤ ((BitVec.ofNat 64 byte.toNat) - 247).toNat ∧
      ((BitVec.ofNat 64 byte.toNat) - 247).toNat ≤ 8 := by
  have byteBound := byte.toBitVec.isLt
  change byte.toNat < 256 at byteBound
  apply rlp_header_length_bytes (BitVec.ofNat 64 byte.toNat) 247 lower
  change byte.toNat % 2^64 ≤ 255
  omega

/-- Every bounded header-length read has the uniform ten-tick call budget
used by item/header parsing, including malformed bytes and exceptions. -/
theorem evaluate_rlpReadLength_header_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length : BitVec 64)
    (small : length.toNat ≤ 8)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "rlp_read_length") arguments)
    state.clock ≤ evaluated.2.clock + 10 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have bound := evaluate_rlpReadLength_call_bounded state arguments pointer length args code (by omega)
  exact ⟨by have cost := bound.1; omega,bound.2.1,bound.2.2⟩

#print axioms rlp_long_string_length_bytes
#print axioms rlp_long_list_length_bytes
#print axioms evaluate_rlpReadLength_header_call_bounded
end InitECandidate.Runtime
