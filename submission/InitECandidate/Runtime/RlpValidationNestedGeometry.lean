import InitECandidate.Runtime.RlpValidationPushInvariant
namespace InitECandidate.Runtime
open Flapjack

/-- A positive non-wrapping header places the nested payload after the parent
cursor and keeps both payload endpoints inside the parent interval. -/
theorem rlpValidation_nested_geometry (position stop header payload : BitVec 64)
    (ordered : position.toNat ≤ stop.toNat) (headerPositive : 0 < header.toNat)
    (sumNoWrap : header.toNat + payload.toNat < 2^64)
    (bounded : (header + payload).toNat ≤ (stop - position).toNat) :
    position.toNat < (position + header).toNat ∧
      (position + header).toNat ≤ (position + header + payload).toNat ∧
      (position + header + payload).toNat ≤ stop.toNat := by
  have remainder : (stop - position).toNat = stop.toNat - position.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr ordered)
  have consumed : (header + payload).toNat = header.toNat + payload.toNat :=
    BitVec.toNat_add_of_lt sumNoWrap
  have stopBound := stop.isLt
  have firstNoWrap : position.toNat + header.toNat < 2^64 := by
    rw [remainder,consumed] at bounded
    omega
  have fullNoWrap : position.toNat + (header + payload).toNat < 2^64 := by
    rw [remainder] at bounded
    omega
  have firstNat := BitVec.toNat_add_of_lt firstNoWrap
  have fullNat := BitVec.toNat_add_of_lt fullNoWrap
  rw [← BitVec.add_assoc] at fullNat
  rw [consumed] at fullNat
  rw [firstNat,fullNat]
  rw [remainder,consumed] at bounded
  omega

/-- A bounded header and an input below the word limit provide the addition
non-wrap condition needed when entering a nested payload. -/
theorem rlpValidation_header_payload_no_wrap (header payload total : BitVec 64)
    (headerSmall : header.toNat ≤ 9) (payloadBound : payload.toNat ≤ total.toNat)
    (inputBound : total.toNat + 9 < 2^64) :
    header.toNat + payload.toNat < 2^64 := by omega

/-- The same header bounds supply exactly the cursor premises for the
checked list-push invariant and its strictly decreasing loop rank. -/
theorem rlpValidation_nested_rank (position stop header payload record : BitVec 64)
    (frames : List RlpValidationFrame) (ordered : position.toNat ≤ stop.toNat)
    (headerPositive : 0 < header.toNat) (headerSmall : header.toNat ≤ 9)
    (payloadBound : payload.toNat ≤ (stop - position).toNat)
    (inputBound : (stop - position).toNat + 9 < 2^64)
    (bounded : (header + payload).toNat ≤ (stop - position).toNat) :
    rlpValidationRank (position + header) (position + header + payload)
      ({record := record,resume := position + header + payload,stop := stop} :: frames) <
      rlpValidationRank position stop frames := by
  have geometry := rlpValidation_nested_geometry position stop header payload ordered headerPositive
    (rlpValidation_header_payload_no_wrap header payload (stop - position) headerSmall payloadBound inputBound) bounded
  exact rlpValidation_rank_push position (position + header) (position + header + payload) stop record frames
    geometry.1 geometry.2.1 geometry.2.2

#print axioms rlpValidation_nested_geometry
#print axioms rlpValidation_header_payload_no_wrap
#print axioms rlpValidation_nested_rank
end InitECandidate.Runtime
