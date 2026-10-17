import InitECandidate.Runtime.HashTableValuesInInsertStores
import InitECandidate.Runtime.HashTableValuesInMoveStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Geometry remains usable after occupancy clearing even before the count
header has been decremented. Only the three pointer-predicate header fields
must still match the original layout. -/
theorem HashTableValuesIn.bookkeeping_word_geometry {F : Type} (geometry state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count destination word : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits geometry)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used) (valuesField : state.memory (table + 40) = .word values)
    (later : order.toNat ≤ destination.toNat) :
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
  exact entries.after_word_separate state table capacity used values destination word targets capField usedField valuesField
    (by intro offset belongs; exact headers offset (by simp at belongs ⊢; omega)) occupancy separateValues

/-- Updating the count header changes none of the header fields, occupancy
bytes, or value cells inspected by registered-value membership. -/
theorem HashTableValuesIn.count_word_geometry {F : Type} (geometry state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count index nextCount : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits geometry)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used) (valuesField : state.memory (table + 40) = .word values)
    (inside : index.toNat < capacity.toNat) :
    HashTableValuesIn table targets (sourceWriteWord state (table + 24) nextCount) := by
  have facts := arrays.insertion_memory geometry keyLength table keys stride capacity used values order orderPos count bits
  obtain ⟨_,_,valueSeparate⟩ := arrays.insert_value_separation_width geometry keyLength table keys stride capacity used values order orderPos count index bits inside
  have headers (offset : Nat) (atHeader : offset ∈ ([16,40,48] : List Nat)) :=
    hashInsert_header_separation_width table keys stride capacity used values order orderPos count keyLength
      arrays.keysAligned arrays.strideAligned arrays.valuesAligned arrays.usedAligned arrays.orderAligned arrays.orderPosAligned
      arrays.headerKeys arrays.headerValues arrays.keysBefore arrays.valuesBefore arrays.usedBefore arrays.orderBefore arrays.endBound
      arrays.fits arrays.room offset (by simp at atHeader; omega) (by simp at atHeader; omega)
  exact entries.after_word_separate state table capacity used values (table + 24) nextCount targets capField usedField valuesField
    (fun offset atHeader => (headers offset atHeader).2.2.2)
    (fun slot bound => (facts.separate index inside slot bound).2.2)
    (fun slot bound => (valueSeparate slot bound).2.2)

#print axioms HashTableValuesIn.bookkeeping_word_geometry
#print axioms HashTableValuesIn.count_word_geometry
end InitECandidate.Runtime
