import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Transfer a two-word field of the payload record across a frame on its
first 80 bytes. The final occupied word starts at offset 72. -/
theorem RlpSliceEntry.after_record_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (post : PanSemStateFiniteExact 64 F) (payload index pointer length : BitVec 64)
    (entry : RlpSliceEntry state payload index pointer length) (indexBound : index.toNat ≤ 4)
    (fits : payload.toNat + 72 < 2 ^ 64) (domain : post.memaddrs = state.memaddrs)
    (frame : ∀ watched : BitVec 64, payload.toNat ≤ watched.toNat → watched.toNat ≤ payload.toNat + 72 →
      post.memory watched = state.memory watched) : RlpSliceEntry post payload index pointer length := by
  have offset : (index * (16#64)).toNat = index.toNat * 16 := by
    apply BitVec.toNat_mul_of_lt
    change index.toNat * 16 < 2 ^ 64
    omega
  have base : (payload + index * (16#64)).toNat = payload.toNat + index.toNat * 16 := by
    rw [BitVec.toNat_add_of_lt (by rw [offset]; omega),offset]
  have last : (payload + index * (16#64) + (8#64)).toNat = payload.toNat + index.toNat * 16 + 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [base]; change _ + 8 < _; omega),base]
    rfl
  exact entry.after_frame state post payload index pointer length domain
    (frame _ (by rw [base]; omega) (by rw [base]; omega))
    (frame _ (by rw [last]; omega) (by rw [last]; omega))

#print axioms RlpSliceEntry.after_record_frame
end InitECandidate.Runtime
