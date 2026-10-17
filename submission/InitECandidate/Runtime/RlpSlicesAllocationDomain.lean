import InitECandidate.Runtime.RlpSliceAddressSeparation
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A nonwrapping slice count passing the real allocator guard gives the
unwrapped byte interval required by the slice-array invariant. -/
theorem rlpSlices_allocation_interval (array count : BitVec 64)
    (arrayBound : array.toNat ≤ 33806089496)
    (countBound : count.toNat * 16 < 2^64)
    (request : count * 16 ≤ (33806089496 : BitVec 64) - array) :
    array.toNat + count.toNat * 16 ≤ 33806089496 := by
  have size : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; exact countBound)]
    rfl
  have allocated := allocationGuard_sum_bound array (count * 16) arrayBound request
  rw [size] at allocated
  exact allocated

/-- A concrete heap arena covering the admitted allocation supplies both
word-store domains for every slice slot. -/
theorem rlpSlices_allocation_domains {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count : BitVec 64)
    (interval : array.toNat + count.toNat * 16 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address) :
    ∀ slot : BitVec 64, slot.toNat < count.toNat →
      state.memaddrs (array + slot * 16#64) ∧ state.memaddrs (array + slot * 16#64 + 8#64) := by
  intro slot inside
  have fits : array.toNat + count.toNat * 16 ≤ 2^64 := by omega
  have second := rlpSlice_cell_toNat array slot count 8 inside (by decide) fits
  have product : (slot * 16#64).toNat = slot.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change slot.toNat * 16 < 2^64; omega)]
    rfl
  have firstNat : (array + slot * 16#64).toNat = array.toNat + slot.toNat * 16 := by
    rw [BitVec.toNat_add_of_lt (by rw [product]; omega),product]
  refine ⟨arena _ ?_ ?_,arena _ ?_ ?_⟩
  · rw [firstNat]; omega
  · rw [firstNat]; omega
  · rw [second]; omega
  · rw [second]; omega

#print axioms rlpSlices_allocation_interval
#print axioms rlpSlices_allocation_domains
end InitECandidate.Runtime
