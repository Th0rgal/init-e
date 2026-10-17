import InitECandidate.Runtime.HashDeleteOrderLinked
import InitECandidate.Runtime.HashReverseEntriesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Swapping the old last order entry into the deleted position puts every
remaining reverse position below the decremented count. -/
theorem HashDeleteOrderLinked.final_swap_reverse_bound {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole deletedPosition lastSlot : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (positive : 0 < items.toNat)
    (deletedBound : deletedPosition.toNat < (items - 1).toNat)
    (lastForward : state.memory (order + (items - 1) * 8) = .word lastSlot)
    (newReverse : post.memory (orderPos + lastSlot * 8) = .word deletedPosition)
    (oldOccupied : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot ≠ some 0 → slot ≠ hole ∧ hashOccupancyRead state used slot ≠ some 0)
    (reverseFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ lastSlot →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8)) :
    HashReverseEntriesBound used orderPos capacity (items - 1) post := by
  have subtraction : (items - (1 : BitVec 64)).toNat = items.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ items.toNat; omega))]
    rfl
  intro slot inside occupied
  by_cases isLast : slot = lastSlot
  · subst slot
    exact ⟨deletedPosition,newReverse,deletedBound⟩
  · obtain ⟨different,before⟩ := oldOccupied slot inside occupied
    obtain ⟨position,bound,_,reverse,forward⟩ := linked slot inside different before
    have notLast : position ≠ items - 1 := by
      intro same
      have unique := linked.position_unique state used order orderPos capacity items hole deletedPosition slot position lastSlot
        inside different before reverse (by rw [same]; exact lastForward)
      exact isLast unique
    have differentNat : position.toNat ≠ (items - 1).toNat := fun same => notLast (BitVec.eq_of_toNat_eq same)
    exact ⟨position,(reverseFrame slot inside isLast).trans reverse,by omega⟩

/-- Deleting the final order position needs no swap; the excluded deleted
position alone supplies the smaller bound. -/
theorem HashDeleteOrderLinked.final_last_reverse_bound {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole (items - 1) state)
    (positive : 0 < items.toNat)
    (oldOccupied : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot ≠ some 0 → slot ≠ hole ∧ hashOccupancyRead state used slot ≠ some 0)
    (reverseFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8)) :
    HashReverseEntriesBound used orderPos capacity (items - 1) post := by
  intro slot inside occupied
  obtain ⟨different,before⟩ := oldOccupied slot inside occupied
  obtain ⟨position,bound,reverse⟩ := linked.last_position_bound state used order orderPos capacity items hole slot
    inside different before positive
  exact ⟨position,(reverseFrame slot inside).trans reverse,bound⟩

#print axioms HashDeleteOrderLinked.final_swap_reverse_bound
#print axioms HashDeleteOrderLinked.final_last_reverse_bound
end InitECandidate.Runtime
