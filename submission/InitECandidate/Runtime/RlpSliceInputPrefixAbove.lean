import InitECandidate.Runtime.RlpSliceInputPrefixBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Slice arrays allocated after a record survive stores below their base. -/
theorem RlpSliceInputPrefix.after_memory_above {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (domain : post.memaddrs = state.memaddrs)
    (memory : ∀ address : BitVec 64, array.toNat ≤ address.toNat → post.memory address = state.memory address) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  intro slot inside
  obtain ⟨pointer,length,entry⟩ := valid slot inside
  have cell0 := rlpSlice_cell_toNat array slot count 0 inside (by decide) fits
  have cell8 := rlpSlice_cell_toNat array slot count 8 inside (by decide) fits
  have above0 : array.toNat ≤ (array + slot * 16#64).toNat := by
    simp only [BitVec.add_zero,Nat.add_zero] at cell0
    rw [cell0]
    omega
  have above8 : array.toNat ≤ (array + slot * 16#64 + 8#64).toNat := by
    rw [cell8]
    omega
  exact ⟨pointer,length,entry.after_frame state post array slot pointer length input inputLength
    domain (memory _ above0) (memory _ above8)⟩

#print axioms RlpSliceInputPrefix.after_memory_above
/-- A slice prefix stored above the scratch ceiling survives any execution
preserving those words and their accessibility. -/
theorem RlpSliceInputPrefix.after_memory_from_ceiling {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count input inputLength : BitVec 64) (ceiling : Nat)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (domain : post.memaddrs = state.memaddrs)
    (memory : ∀ address : BitVec 64, ceiling ≤ address.toNat → post.memory address = state.memory address) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  intro slot inside
  obtain ⟨pointer,length,entry⟩ := valid slot inside
  have cell0 := rlpSlice_cell_toNat array slot count 0 inside (by decide) fits
  have cell8 := rlpSlice_cell_toNat array slot count 8 inside (by decide) fits
  have above0 : ceiling ≤ (array + slot * 16#64).toNat := by
    simp only [BitVec.add_zero,Nat.add_zero] at cell0
    rw [cell0]
    omega
  have above8 : ceiling ≤ (array + slot * 16#64 + 8#64).toNat := by
    rw [cell8]
    omega
  exact ⟨pointer,length,RlpSliceInputEntry.after_frame state post array slot pointer length input inputLength
    entry domain (memory _ above0) (memory _ above8)⟩


#print axioms RlpSliceInputPrefix.after_memory_from_ceiling
end InitECandidate.Runtime
