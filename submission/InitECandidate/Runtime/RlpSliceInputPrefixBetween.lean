import InitECandidate.Runtime.RlpSliceInputPrefixBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An old slice array survives writes below its lower boundary and above its
upper boundary, without placing the array below the scratch frame. -/
theorem RlpSliceInputPrefix.after_memory_between {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count input inputLength upper : BitVec 64) (lower : Nat)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (above : lower ≤ array.toNat) (before : array.toNat + count.toNat * 16 ≤ upper.toNat)
    (domain : post.memaddrs = state.memaddrs)
    (memory : ∀ address : BitVec 64, address.toNat < upper.toNat → lower ≤ address.toNat →
      post.memory address = state.memory address) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  intro slot inside
  obtain ⟨pointer,length,entry⟩ := valid slot inside
  have fits : array.toNat + count.toNat * 16 ≤ 2^64 := by have top := upper.isLt; omega
  have cell0 := rlpSlice_cell_toNat array slot count 0 inside (by decide) fits
  have cell8 := rlpSlice_cell_toNat array slot count 8 inside (by decide) fits
  have first : lower ≤ (array + slot * 16#64).toNat ∧ (array + slot * 16#64).toNat < upper.toNat := by
    simp only [BitVec.add_zero,Nat.add_zero] at cell0
    rw [cell0]
    omega
  have second : lower ≤ (array + slot * 16#64 + 8#64).toNat ∧ (array + slot * 16#64 + 8#64).toNat < upper.toNat := by
    rw [cell8]
    omega
  exact ⟨pointer,length,entry.after_frame state post array slot pointer length input inputLength
    domain (memory _ first.2 first.1) (memory _ second.2 second.1)⟩

#print axioms RlpSliceInputPrefix.after_memory_between
end InitECandidate.Runtime
