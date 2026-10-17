import InitECandidate.Runtime.HashValueWriteGeometry32
import InitECandidate.Runtime.HashTableArraysRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- All value-cell separation obligations in the insertion suffix follow
from the table layout; occupied values require no further aliasing premise. -/
theorem HashTableArraysInvariant.insert_value_separation_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count inserted : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (inside : inserted.toNat < capacity.toNat) :
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ inserted →
      values + slot * 8 ≠ values + inserted * 8) ∧
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ panByteAlignHOL (used + inserted)) ∧
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + count * 8 ∧
      values + slot * 8 ≠ orderPos + inserted * 8 ∧ values + slot * 8 ≠ table + 24) := by
  have hv := invariant.headerValues
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have address : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      (values + slot * 8).toNat = values.toNat + slot.toNat * 8 := by
    intro slot bound
    exact (hashFind_slot_address values slot 8 capacity bound
      (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
      invariant.valuesAligned (by decide)).1
  have oa := (hashFind_slot_address order count 8 capacity invariant.room
    (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have ra := (hashFind_slot_address orderPos inserted 8 capacity inside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded) invariant.orderPosAligned (by decide)).1
  change (order + count * 8).toNat = order.toNat + count.toNat * 8 at oa
  change (orderPos + inserted * 8).toNat = orderPos.toNat + inserted.toNat * 8 at ra
  have ha : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro slot bound different same
    have natural := congrArg BitVec.toNat same
    rw [address slot bound,address inserted inside] at natural
    exact different (BitVec.eq_of_toNat_eq (by omega))
  · intro slot bound
    exact Ne.symm (hashSet_value_separate values used capacity slot bound invariant.valuesAligned
      invariant.usedAligned vu (by omega) inserted inside)
  · intro slot bound
    have va := address slot bound
    have product := Nat.mul_lt_mul_of_pos_right bound (by decide : 0 < 8)
    refine ⟨?_,?_,?_⟩ <;> intro same <;> have natural := congrArg BitVec.toNat same
    · rw [va,oa] at natural; omega
    · rw [va,ra] at natural; omega
    · rw [va,ha] at natural; omega

#print axioms HashTableArraysInvariant.insert_value_separation_width
end InitECandidate.Runtime
