import InitECandidate.Runtime.HashOrderInsertGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every live forward cell is separated from the header and reverse array;
distinct forward positions also have distinct addresses. -/
theorem HashTableArraysInvariant.delete_final_order_separation_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items deletedPosition lastSlot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (deletedInside : deletedPosition.toNat < items.toNat) (lastInside : lastSlot.toNat < capacity.toNat) :
    (order + deletedPosition * 8 ≠ orderPos + lastSlot * 8 ∧ order + deletedPosition * 8 ≠ table + 24) ∧
    (∀ position : BitVec 64, position.toNat < items.toNat →
      order + position * 8 ≠ table + 24 ∧ (position ≠ deletedPosition →
        order + position * 8 ≠ order + deletedPosition * 8 ∧ order + position * 8 ≠ orderPos + lastSlot * 8)) := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have address : ∀ position : BitVec 64, position.toNat < capacity.toNat →
      (order + position * 8).toNat = order.toNat + position.toNat * 8 := by
    intro position bound
    exact (hashFind_slot_address order position 8 capacity bound
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have ra := (hashFind_slot_address orderPos lastSlot 8 capacity lastInside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded) invariant.orderPosAligned (by decide)).1
  change (orderPos + lastSlot * 8).toNat = orderPos.toNat + lastSlot.toNat * 8 at ra
  have ha : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
    rfl
  have separate : ∀ position : BitVec 64, position.toNat < items.toNat →
      order + position * 8 ≠ orderPos + lastSlot * 8 ∧ order + position * 8 ≠ table + 24 := by
    intro position bound
    have inside : position.toNat < capacity.toNat := by omega
    have oa := address position inside
    have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
    constructor <;> intro same <;> have natural := congrArg BitVec.toNat same
    · rw [oa,ra] at natural; omega
    · rw [oa,ha] at natural; omega
  refine ⟨separate deletedPosition deletedInside,?_⟩
  intro position before
  refine ⟨(separate position before).2,?_⟩
  intro different
  refine ⟨?_,(separate position before).1⟩
  intro same
  have natural := congrArg BitVec.toNat same
  rw [address position (by omega),address deletedPosition (by omega)] at natural
  exact different (BitVec.eq_of_toNat_eq (by omega))

#print axioms HashTableArraysInvariant.delete_final_order_separation_width
end InitECandidate.Runtime
