import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A frame on the concrete slice-table interval retains every readable
entry and its original input-span bound. -/
theorem RlpSliceInputPrefix.after_interval_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array input inputLength : BitVec 64) (count : Nat)
    (valid : RlpSliceInputPrefix state array input inputLength count)
    (fits : array.toNat + count * 16 < 2 ^ 64) (domain : post.memaddrs = state.memaddrs)
    (frame : ∀ watched : BitVec 64, array.toNat ≤ watched.toNat → watched.toNat < array.toNat + count * 16 →
      post.memory watched = state.memory watched) : RlpSliceInputPrefix post array input inputLength count := by
  intro slot inside
  obtain ⟨pointer,length,entry⟩ := valid slot inside
  have offset : (slot * (16#64)).toNat = slot.toNat * 16 := by
    apply BitVec.toNat_mul_of_lt
    change slot.toNat * 16 < 2 ^ 64
    omega
  have base : (array + slot * (16#64)).toNat = array.toNat + slot.toNat * 16 := by
    rw [BitVec.toNat_add_of_lt (by rw [offset]; omega),offset]
  have last : (array + slot * (16#64) + (8#64)).toNat = array.toNat + slot.toNat * 16 + 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [base]; change _ + 8 < _; omega),base]
    rfl
  exact ⟨pointer,length,entry.after_frame state post array slot pointer length input inputLength domain
    (frame _ (by rw [base]; omega) (by rw [base]; omega))
    (frame _ (by rw [last]; omega) (by rw [last]; omega))⟩

#print axioms RlpSliceInputPrefix.after_interval_frame
end InitECandidate.Runtime
