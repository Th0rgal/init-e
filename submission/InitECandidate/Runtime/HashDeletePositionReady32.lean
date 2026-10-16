import InitECandidate.Runtime.HashReverseEntriesBound
import InitECandidate.Runtime.HashTableArraysRead32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An occupied scanned slot supplies a bounded reverse position and the
actual domains needed for its position read and subsequent order write. -/
theorem HashTableArraysInvariant32.delete_position_ready {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count scan : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (reverse : HashReverseEntriesBound used orderPos capacity count state)
    (scanInside : scan.toNat < capacity.toNat)
    (occupied : hashOccupancyRead state used scan ≠ some 0) :
    ∃ position : BitVec 64, state.memory (orderPos + scan * 8) = .word position ∧
      position.toNat < count.toNat ∧ state.memaddrs (orderPos + scan * 8) ∧
      state.memaddrs (order + position * 8) := by
  obtain ⟨position,cell,bound⟩ := reverse scan scanInside occupied
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have limit := invariant.endBound
  have room := invariant.room
  have scanAddress := (hashFind_slot_address orderPos scan 8 capacity scanInside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact limit)
    invariant.orderPosAligned (by decide)).1
  have positionAddress := (hashFind_slot_address order position 8 capacity (by omega)
    (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
    invariant.orderAligned (by decide)).1
  change (orderPos + scan * 8).toNat = orderPos.toNat + scan.toNat * 8 at scanAddress
  change (order + position * 8).toNat = order.toNat + position.toNat * 8 at positionAddress
  have scanProduct := Nat.mul_lt_mul_of_pos_right scanInside (by decide : 0 < 8)
  have positionProduct := Nat.mul_lt_mul_of_pos_right (show position.toNat < capacity.toNat by omega) (by decide : 0 < 8)
  refine ⟨position,cell,bound,?_,?_⟩
  · apply invariant.domain <;> omega
  · apply invariant.domain <;> omega

#print axioms HashTableArraysInvariant32.delete_position_ready
end InitECandidate.Runtime
