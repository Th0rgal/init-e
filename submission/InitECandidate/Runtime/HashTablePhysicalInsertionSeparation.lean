import InitECandidate.Runtime.HashTablePhysicalFrame
import InitECandidate.Runtime.HashTableOutsideHeaderRegionSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashTableArraysInvariant.outside_physical_word_separation_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count watched : BitVec 64) (bits : Nat)
    (valid : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (outside : ¬tablePhysicalRegion table keys stride capacity used values order orderPos watched) :
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < keyLength.toNat →
      watched ≠ keys + slot * stride + BitVec.ofNat 64 offset ∧
      watched ≠ panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)) ∧
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ values + slot * 8 ∧
      watched ≠ panByteAlignHOL (used + slot) ∧ watched ≠ orderPos + slot * 8) ∧
    watched ≠ order + count * 8 ∧ watched ≠ table + 24 := by
  have hk := valid.headerKeys
  have hv := valid.headerValues
  have ku := valid.keysBefore
  have vu := valid.valuesBefore
  have uo := valid.usedBefore
  have oo := valid.orderBefore
  have limit := valid.endBound
  have wordMember : ∀ base : BitVec 64, base.toNat % 8 = 0 → base.toNat + capacity.toNat * 8 ≤ 33806089496 →
      (∀ address : BitVec 64, base.toNat ≤ address.toNat → address.toNat < base.toNat + capacity.toNat * 8 →
        tablePhysicalRegion table keys stride capacity used values order orderPos address) →
      ∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ base + slot * 8 := by
    intro base aligned bound region slot inside same
    have address := (hashFind_slot_address base slot 8 capacity inside
      (by change base.toNat + capacity.toNat * 8 ≤ 33806089496; exact bound) aligned (by decide)).1
    change (base + slot * 8).toNat = base.toNat + slot.toNat * 8 at address
    have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
    apply outside
    rw [same]
    exact region _ (by omega) (by omega)
  refine ⟨?_,?_,?_,?_⟩
  · intro slot inside
    have address := hashFind_slot_address keys slot stride capacity inside (by omega) valid.keysAligned valid.strideAligned
    have next := Nat.mul_le_mul_right stride.toNat (show slot.toNat + 1 ≤ capacity.toNat by omega)
    rw [Nat.add_mul,Nat.one_mul] at next
    have fits := valid.fits
    apply memcpy_interval_separate (keys + slot * stride) keyLength watched address.2 (by omega)
    have notKeys : ¬(keys.toNat ≤ watched.toNat ∧ watched.toNat < keys.toNat + capacity.toNat * stride.toNat) := by
      intro member
      exact outside (Or.inr (Or.inl member))
    omega
  · intro slot inside
    refine ⟨wordMember values valid.valuesAligned (by omega) (by intro address lower upper; unfold tablePhysicalRegion; omega) slot inside,?_,
      wordMember orderPos valid.orderPosAligned limit (by intro address lower upper; unfold tablePhysicalRegion; omega) slot inside⟩
    intro same
    have interval := hashOccupancy_aligned_interval used capacity slot valid.usedAligned (by omega) inside
    apply outside
    rw [same]
    unfold tablePhysicalRegion
    omega
  · exact wordMember order valid.orderAligned (by omega) (by intro address lower upper; unfold tablePhysicalRegion; omega) count valid.room
  · intro same
    have header : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
      rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
      rfl
    apply outside
    rw [same]
    exact Or.inl ⟨by omega,by omega⟩

#print axioms HashTableArraysInvariant.outside_physical_word_separation_width
end InitECandidate.Runtime
