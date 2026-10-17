import InitECandidate.Runtime.HashValueEntriesWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- During deletion the hole remains marked occupied, but its old order
position is being removed. All other occupied slots retain a matching forward
entry and a reverse position distinct from the deleted position. -/
def HashDeleteOrderLinked {F : Type}
    (used order orderPos capacity items hole deletedPosition : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
    hashOccupancyRead state used slot ≠ some 0 →
    ∃ position : BitVec 64, position.toNat < items.toNat ∧ position ≠ deletedPosition ∧
      state.memory (orderPos + slot * 8) = .word position ∧
      state.memory (order + position * 8) = .word slot

/-- A forward load identifies the unique remaining slot with that reverse
position. This is the missing link needed to shrink the bound after a swap. -/
theorem HashDeleteOrderLinked.position_unique {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole deletedPosition slot position lastSlot : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (inside : slot.toNat < capacity.toNat) (different : slot ≠ hole)
    (occupied : hashOccupancyRead state used slot ≠ some 0)
    (reverse : state.memory (orderPos + slot * 8) = .word position)
    (forward : state.memory (order + position * 8) = .word lastSlot) : slot = lastSlot := by
  obtain ⟨actual,_,_,cell,matching⟩ := linked slot inside different occupied
  have equal : actual = position := by have words := cell.symm.trans reverse; injection words
  rw [equal] at matching
  have words := matching.symm.trans forward
  injection words

/-- If the deleted position is the last one, every other occupied reverse
position already lies below the decremented count. -/
theorem HashDeleteOrderLinked.last_position_bound {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole slot : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole (items - 1) state)
    (inside : slot.toNat < capacity.toNat) (different : slot ≠ hole)
    (occupied : hashOccupancyRead state used slot ≠ some 0) (positive : 0 < items.toNat) :
    ∃ position : BitVec 64, position.toNat < (items - 1).toNat ∧
      state.memory (orderPos + slot * 8) = .word position := by
  obtain ⟨position,bound,notDeleted,cell,_⟩ := linked slot inside different occupied
  have subtraction : (items - (1 : BitVec 64)).toNat = items.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ items.toNat; omega))]
    rfl
  have differentNat : position.toNat ≠ (items - 1).toNat := fun same => notDeleted (BitVec.eq_of_toNat_eq same)
  exact ⟨position,by omega,cell⟩

#print axioms HashDeleteOrderLinked.position_unique
#print axioms HashDeleteOrderLinked.last_position_bound
end InitECandidate.Runtime
