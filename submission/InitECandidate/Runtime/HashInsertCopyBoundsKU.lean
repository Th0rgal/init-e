import InitECandidate.Runtime.HashInsertCopyBounds
import InitECandidate.Runtime.PtKeyULeafKUGD
import InitECandidate.Runtime.HashInsertProbeTailKU
/-! Unaligned-key copy of `HashInsertCopyBounds` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every in-range slot of an aligned, allocated key array supplies the actual
copy bounds and domains needed by insertion, including aligned byte cells. -/
theorem hashInsert_copy_bounds_from_arrayKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride key keyLength used capacity : BitVec 64)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496) (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ keys.toNat)
    (keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat)
    (usedBound : used.toNat + capacity.toNat ≤ 33806089496)
    (fits : keyLength.toNat ≤ stride.toNat)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∀ index : BitVec 64, index.toNat < capacity.toNat → HashInsertCopyBoundsKU table keys stride key keyLength used capacity index state := by
  intro index inside
  have bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496 := by omega
  have slot := hashFind_slot_address keys index stride capacity inside bounded keysAligned strideAligned
  have nextIndex : index.toNat + 1 ≤ capacity.toNat := by omega
  have nextProduct := Nat.mul_le_mul_right stride.toNat nextIndex
  rw [Nat.add_mul,Nat.one_mul] at nextProduct
  have endBound : (keys + index * stride).toNat + keyLength.toNat ≤ keys.toNat + capacity.toNat * stride.toNat := by
    rw [slot.1]
    omega
  refine ⟨by omega,slot.2,keyAligned,len8,keyFit,usedAligned,?_,by omega,usedBound,?_,?_,sourceWordDomain,sourceByteDomain⟩
  · rw [slot.1]; omega
  · intro offset offsetInside
    have interval := hashFind_slot_offset keys index stride capacity keyLength offset inside bounded keysAligned strideAligned fits offsetInside
    exact arrayDomain _ interval.2.1 interval.2.2
  · intro offset offsetInside
    have small : offset < 2 ^ 64 := Nat.lt_trans offsetInside keyLength.isLt
    have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt small
    have interval := hashOccupancy_aligned_interval (keys + index * stride) keyLength (BitVec.ofNat 64 offset) slot.2
      (by omega) (by rw [offsetNat]; exact offsetInside)
    apply arrayDomain
    · have lower : keys.toNat ≤ (keys + index * stride).toNat := by rw [slot.1]; omega
      omega
    · omega

#print axioms hashInsert_copy_bounds_from_arrayKU
end InitECandidate.Runtime
