import InitECandidate.Runtime.HashDeleteFinalReverseBound
import InitECandidate.Runtime.HashOrderLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The final order swap restores both directions of the live order link
under the decremented count. -/
theorem HashDeleteOrderLinked.final_swap_linked {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole deletedPosition lastSlot : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (positive : 0 < items.toNat) (deletedBound : deletedPosition.toNat < (items - 1).toNat)
    (lastForward : state.memory (order + (items - 1) * 8) = .word lastSlot)
    (newReverse : post.memory (orderPos + lastSlot * 8) = .word deletedPosition)
    (newForward : post.memory (order + deletedPosition * 8) = .word lastSlot)
    (oldOccupied : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot ≠ some 0 → slot ≠ hole ∧ hashOccupancyRead state used slot ≠ some 0)
    (reverseFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ lastSlot →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8))
    (forwardFrame : ∀ position : BitVec 64, position.toNat < items.toNat → position ≠ deletedPosition →
      post.memory (order + position * 8) = state.memory (order + position * 8)) :
    HashOrderLinked used order orderPos capacity (items - 1) post := by
  have subtraction : (items - (1 : BitVec 64)).toNat = items.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ items.toNat; omega))]
    rfl
  intro slot inside occupied
  by_cases isLast : slot = lastSlot
  · subst slot
    exact ⟨deletedPosition,deletedBound,newReverse,newForward⟩
  · obtain ⟨different,before⟩ := oldOccupied slot inside occupied
    obtain ⟨position,bound,notDeleted,reverse,forward⟩ := linked slot inside different before
    have notLast : position ≠ items - 1 := by
      intro same
      exact isLast (linked.position_unique state used order orderPos capacity items hole deletedPosition slot position lastSlot
        inside different before reverse (by rw [same]; exact lastForward))
    have differentNat : position.toNat ≠ (items - 1).toNat := fun same => notLast (BitVec.eq_of_toNat_eq same)
    exact ⟨position,by omega,(reverseFrame slot inside isLast).trans reverse,
      (forwardFrame position bound notDeleted).trans forward⟩

/-- Removing the last position restores linkage without changing any order pair. -/
theorem HashDeleteOrderLinked.final_last_linked {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole (items - 1) state)
    (positive : 0 < items.toNat)
    (oldOccupied : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot ≠ some 0 → slot ≠ hole ∧ hashOccupancyRead state used slot ≠ some 0)
    (reverseFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8))
    (forwardFrame : ∀ position : BitVec 64, position.toNat < items.toNat →
      post.memory (order + position * 8) = state.memory (order + position * 8)) :
    HashOrderLinked used order orderPos capacity (items - 1) post := by
  have subtraction : (items - (1 : BitVec 64)).toNat = items.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ items.toNat; omega))]
    rfl
  intro slot inside occupied
  obtain ⟨different,before⟩ := oldOccupied slot inside occupied
  obtain ⟨position,bound,notDeleted,reverse,forward⟩ := linked slot inside different before
  have differentNat : position.toNat ≠ (items - 1).toNat := fun same => notDeleted (BitVec.eq_of_toNat_eq same)
  exact ⟨position,by omega,(reverseFrame slot inside).trans reverse,(forwardFrame position bound).trans forward⟩

#print axioms HashDeleteOrderLinked.final_swap_linked
#print axioms HashDeleteOrderLinked.final_last_linked
end InitECandidate.Runtime
