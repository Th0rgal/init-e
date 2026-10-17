import InitECandidate.Runtime.RlpSliceInputPrefix
import InitECandidate.Runtime.RlpSliceAddressSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A slice prefix stored below the scratch frame survives any execution
preserving those words and their accessibility. -/
theorem RlpSliceInputPrefix.after_memory_below {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count input inputLength frame : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (domain : post.memaddrs = state.memaddrs)
    (memory : ∀ address : BitVec 64, address.toNat < frame.toNat → post.memory address = state.memory address) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  have fits : array.toNat + count.toNat * 16 ≤ 2^64 := Nat.le_trans before (Nat.le_of_lt frame.isLt)
  intro slot inside
  obtain ⟨pointer,length,entry⟩ := valid slot inside
  have cell0 := rlpSlice_cell_toNat array slot count 0 inside (by decide) fits
  have cell8 := rlpSlice_cell_toNat array slot count 8 inside (by decide) fits
  have below0 : (array + slot * 16#64).toNat < frame.toNat := by
    simp only [BitVec.add_zero,Nat.add_zero] at cell0
    rw [cell0]
    omega
  have below8 : (array + slot * 16#64 + 8#64).toNat < frame.toNat := by
    rw [cell8]
    omega
  exact ⟨pointer,length,RlpSliceInputEntry.after_frame state post array slot pointer length input inputLength
    entry domain (memory _ below0) (memory _ below8)⟩

#print axioms RlpSliceInputPrefix.after_memory_below
end InitECandidate.Runtime
