import InitECandidate.Runtime.RlpHeaderCallSizedMemory
import InitECandidate.Runtime.RlpValidationNestedGeometry
namespace InitECandidate.Runtime
open Flapjack

/-- Sized progress exposes bounds for the exact returned fields. -/
theorem RlpHeaderSizedProgress.fields (header payload kind length : BitVec 64)
    (valid : RlpHeaderSizedProgress (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) length) :
    (kind = 0 ∨ kind = 1) ∧ header.toNat ≤ 9 ∧ payload.toNat ≤ length.toNat ∧
      0 < (header + payload).toNat ∧ (header + payload).toNat ≤ length.toNat ∧
      (kind = 1 → 0 < header.toNat ∧ payload.toNat < length.toNat) := by
  obtain ⟨progress,sizes⟩ := valid
  obtain ⟨h,n,k,shape,small,bounded,positiveHeader⟩ := sizes
  simp only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,and_true] at shape
  obtain ⟨rfl,rfl,rfl⟩ := shape
  obtain ⟨h,n,k,shape,flag,positive,consumed,nested⟩ := progress
  simp only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,and_true] at shape
  obtain ⟨rfl,rfl,rfl⟩ := shape
  exact ⟨flag,small,bounded,positive,consumed,by intro list; exact ⟨positiveHeader list,nested list⟩⟩

/-- The checked header predicate alone supplies non-wrapping nested cursors
for the list continuation; source execution has already established its facts. -/
theorem RlpHeaderSizedProgress.list_geometry (position stop header payload : BitVec 64)
    (valid : RlpHeaderSizedProgress (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]) (stop - position))
    (ordered : position.toNat ≤ stop.toNat) (inputBound : (stop - position).toNat + 9 < 2^64) :
    position.toNat < (position + header).toNat ∧
      (position + header).toNat ≤ (position + header + payload).toNat ∧
      (position + header + payload).toNat ≤ stop.toNat := by
  have fields := valid.fields header payload 1 (stop - position)
  exact rlpValidation_nested_geometry position stop header payload ordered (fields.2.2.2.2.2 rfl).1
    (rlpValidation_header_payload_no_wrap header payload (stop - position) fields.2.1 fields.2.2.1 inputBound)
    fields.2.2.2.2.1

/-- Every sized header advances the outer cursor within the input interval. -/
theorem RlpHeaderSizedProgress.cursor (position stop header payload kind : BitVec 64)
    (valid : RlpHeaderSizedProgress (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) (stop - position))
    (ordered : position.toNat ≤ stop.toNat) :
    position.toNat < (position + header + payload).toNat ∧
      (position + header + payload).toNat ≤ stop.toNat := by
  have fields := valid.fields header payload kind (stop - position)
  have geometry := rlp_header_cursor_advance position stop header payload ordered fields.2.2.2.1 fields.2.2.2.2.1
  exact ⟨geometry.1,geometry.2.1⟩

#print axioms RlpHeaderSizedProgress.fields
#print axioms RlpHeaderSizedProgress.list_geometry
#print axioms RlpHeaderSizedProgress.cursor
end InitECandidate.Runtime
