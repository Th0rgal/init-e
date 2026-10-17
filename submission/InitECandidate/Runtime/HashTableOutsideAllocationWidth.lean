import InitECandidate.Runtime.HashTableOutsideHeaderRegionSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Insertion writes stay within the enclosing table allocation. This includes
watched words after the table, which the earlier-array frame does not cover. -/
theorem HashTableArraysInvariant.outside_allocation_word_separation_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count watched : BitVec 64) (bits : Nat)
    (valid : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (outside : watched.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ watched.toNat) :
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
  rcases outside with before | after
  · exact valid.outside_header_word_separation_width state keyLength table keys stride capacity used values order orderPos count watched bits table.toNat
      (by omega) (by omega) (Or.inl before) before
  · have wordUpper : ∀ base : BitVec 64, base.toNat % 8 = 0 →
        base.toNat + capacity.toNat * 8 ≤ orderPos.toNat + capacity.toNat * 8 →
        ∀ slot : BitVec 64, slot.toNat < capacity.toNat → (base + slot * 8).toNat < orderPos.toNat + capacity.toNat * 8 := by
      intro base aligned bound slot inside
      have address := (hashFind_slot_address base slot 8 capacity inside (by change base.toNat + capacity.toNat * 8 ≤ 33806089496; omega) aligned (by decide)).1
      change (base + slot * 8).toNat = base.toNat + slot.toNat * 8 at address
      have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
      omega
    refine ⟨?_,?_,?_,?_⟩
    · intro slot inside
      have address := hashFind_slot_address keys slot stride capacity inside (by omega) valid.keysAligned valid.strideAligned
      have next := Nat.mul_le_mul_right stride.toNat (show slot.toNat + 1 ≤ capacity.toNat by omega)
      rw [Nat.add_mul,Nat.one_mul] at next
      have fits := valid.fits
      apply memcpy_interval_separate (keys + slot * stride) keyLength watched address.2 (by omega)
      exact Or.inr (by omega)
    · intro slot inside
      have valueUpper := wordUpper values valid.valuesAligned (by omega) slot inside
      have reverseUpper := wordUpper orderPos valid.orderPosAligned (by omega) slot inside
      have usedInterval := hashOccupancy_aligned_interval used capacity slot valid.usedAligned (by omega) inside
      refine ⟨?_,?_,?_⟩ <;> intro same <;> have natural := congrArg BitVec.toNat same <;> omega
    · have orderUpper := wordUpper order valid.orderAligned (by omega) count valid.room
      intro same
      have natural := congrArg BitVec.toNat same
      omega
    · have header : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
        rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
        rfl
      intro same
      have natural := congrArg BitVec.toNat same
      omega

#print axioms HashTableArraysInvariant.outside_allocation_word_separation_width
end InitECandidate.Runtime
