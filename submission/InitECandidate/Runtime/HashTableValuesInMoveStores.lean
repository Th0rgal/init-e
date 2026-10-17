import InitECandidate.Runtime.HashTableValuesInExisting
import InitECandidate.Runtime.HashTableValuesInStores
import InitECandidate.Runtime.HashTableArraysMoveStoresWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Stores in the order/reverse region cannot overwrite headers, occupancy,
or registered value cells. -/
theorem HashTableArraysInvariant.bookkeeping_word_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count destination word : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (later : order.toNat ≤ destination.toNat) :
    HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits (sourceWriteWord state destination word) ∧
    HashTableValuesIn table targets (sourceWriteWord state destination word) := by
  have hv := arrays.headerValues
  have vu := arrays.valuesBefore
  have uo := arrays.usedBefore
  have oo := arrays.orderBefore
  have limit := arrays.endBound
  have headers : ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat), table + BitVec.ofNat 64 offset ≠ destination := by
    intro offset belongs same
    have small : offset ≤ 64 := by simp at belongs; omega
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have location : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    have equal := congrArg BitVec.toNat same
    omega
  have occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ destination := by
    intro slot inside same
    have interval := hashOccupancy_aligned_interval used capacity slot arrays.usedAligned (by omega) inside
    have equal := congrArg BitVec.toNat same
    omega
  have separateValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ destination := by
    intro slot inside same
    have location := (hashFind_slot_address values slot 8 capacity inside
      (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega) arrays.valuesAligned (by decide)).1
    change (values + slot * 8).toNat = values.toNat + slot.toNat * 8 at location
    have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
    have equal := congrArg BitVec.toNat same
    omega
  exact ⟨arrays.after_word_width state keyLength table keys stride capacity used values order orderPos count destination word bits headers occupancy,
    entries.after_word_separate state table capacity used values destination word targets arrays.cell16 arrays.cell48 arrays.cell40
      (by intro offset belongs; exact headers offset (by simp at belongs ⊢; omega)) occupancy separateValues⟩

/-- Moving a registered value into a hole and updating order bookkeeping
preserves registered values for every occupied slot. -/
theorem HashTableValuesIn.move_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count hole position value : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (member : value ∈ targets) (holeInside : hole.toNat < capacity.toNat) (positionBound : position.toNat < count.toNat) :
    HashTableValuesIn table targets
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
        (order + position * 8) hole) (orderPos + hole * 8) position) := by
  have written := arrays.write_value_width state keyLength table keys stride capacity used values order orderPos count hole value bits holeInside
  have registered := entries.write_value_layout state keyLength table keys stride capacity used values order orderPos count hole value bits arrays targets member holeInside
  have vu := arrays.valuesBefore
  have uo := arrays.usedBefore
  have oo := arrays.orderBefore
  have limit := arrays.endBound
  have positionInside := Nat.lt_trans positionBound arrays.room
  have oa := (hashFind_slot_address order position 8 capacity positionInside (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) arrays.orderAligned (by decide)).1
  have ra := (hashFind_slot_address orderPos hole 8 capacity holeInside (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact limit) arrays.orderPosAligned (by decide)).1
  change (order + position * 8).toNat = order.toNat + position.toNat * 8 at oa
  change (orderPos + hole * 8).toNat = orderPos.toNat + hole.toNat * 8 at ra
  obtain ⟨second,secondRegistered⟩ := written.bookkeeping_word_values_in _ keyLength table keys stride capacity used values order orderPos count (order + position * 8) hole bits targets registered (by omega)
  exact (second.bookkeeping_word_values_in _ keyLength table keys stride capacity used values order orderPos count (orderPos + hole * 8) position bits targets secondRegistered (by omega)).2

#print axioms HashTableArraysInvariant.bookkeeping_word_values_in
#print axioms HashTableValuesIn.move_stores
end InitECandidate.Runtime
