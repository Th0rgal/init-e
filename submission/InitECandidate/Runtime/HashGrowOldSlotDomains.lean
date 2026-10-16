import InitECandidate.Runtime.HashInsertCopyBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A valid old order entry supplies all actual rehash reads from bounded
allocated key/value arrays, including aligned byte loads in memcpy. -/
theorem hashGrow_old_slot_domains {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride values capacity slot : BitVec 64)
    (inside : slot.toNat < capacity.toNat)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (valuesAligned : values.toNat % 8 = 0) (fits : 32 ≤ stride.toNat)
    (keyBound : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (valueBound : values.toNat + capacity.toNat * 8 ≤ 33806089496)
    (keyDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (valueDomain : ∀ address : BitVec 64, values.toNat ≤ address.toNat →
      address.toNat < values.toNat + capacity.toNat * 8 → state.memaddrs address) :
    (keys + slot * stride).toNat % 8 = 0 ∧
      (∀ offset : Nat, offset < 32 → state.memaddrs (keys + slot * stride + BitVec.ofNat 64 offset)) ∧
      (∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset))) ∧
      state.memaddrs (values + slot * 8) := by
  have selected := hashFind_slot_address keys slot stride capacity inside keyBound keysAligned strideAligned
  have next := Nat.mul_le_mul_right stride.toNat (show slot.toNat + 1 ≤ capacity.toNat by omega)
  rw [Nat.add_mul,Nat.one_mul] at next
  have endBound : (keys + slot * stride).toNat + 32 ≤ keys.toNat + capacity.toNat * stride.toNat := by
    rw [selected.1]
    omega
  refine ⟨selected.2,?_,?_,?_⟩
  · intro offset offsetInside
    have interval := hashFind_slot_offset keys slot stride capacity 32 offset inside keyBound keysAligned strideAligned fits offsetInside
    exact keyDomain _ interval.2.1 interval.2.2
  · intro offset offsetInside
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have interval := hashOccupancy_aligned_interval (keys + slot * stride) 32 (BitVec.ofNat 64 offset) selected.2
      (by change (keys + slot * stride).toNat + 32 ≤ 2 ^ 64; omega)
      (by rw [natural]; exact offsetInside)
    change (keys + slot * stride).toNat ≤ (panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)).toNat ∧
      (panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)).toNat < (keys + slot * stride).toNat + 32 at interval
    apply keyDomain
    · have lower : keys.toNat ≤ (keys + slot * stride).toNat := by rw [selected.1]; omega
      omega
    · change (panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)).toNat < keys.toNat + capacity.toNat * stride.toNat
      omega
  · have interval := hashFind_slot_offset values slot 8 capacity 8 0 inside
      (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; exact valueBound)
      valuesAligned (by decide) (by decide) (by decide)
    apply valueDomain
    · simpa using interval.2.1
    · simpa using interval.2.2

#print axioms hashGrow_old_slot_domains
end InitECandidate.Runtime
