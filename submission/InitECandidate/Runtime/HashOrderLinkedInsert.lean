import InitECandidate.Runtime.HashOrderLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A newly occupied slot and its appended forward/reverse cells extend the
live link; all prior occupied slots retain their existing matching pair. -/
theorem HashOrderLinked.insert {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items inserted : BitVec 64)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (noWrap : items.toNat + 1 < 2 ^ 64)
    (newReverse : post.memory (orderPos + inserted * 8) = .word items)
    (newForward : post.memory (order + items * 8) = .word inserted)
    (oldOccupied : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ inserted →
      hashOccupancyRead post used slot ≠ some 0 → hashOccupancyRead state used slot ≠ some 0)
    (reverseFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ inserted →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8))
    (forwardFrame : ∀ position : BitVec 64, position.toNat < items.toNat →
      post.memory (order + position * 8) = state.memory (order + position * 8)) :
    HashOrderLinked used order orderPos capacity (items + 1) post := by
  have increment : (items + (1 : BitVec 64)).toNat = items.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change items.toNat + 1 < 2 ^ 64; exact noWrap)]
    rfl
  intro slot inside occupied
  by_cases same : slot = inserted
  · subst slot
    exact ⟨items,by omega,newReverse,newForward⟩
  · obtain ⟨position,bound,reverse,forward⟩ := linked slot inside (oldOccupied slot inside same occupied)
    exact ⟨position,by omega,(reverseFrame slot inside same).trans reverse,(forwardFrame position bound).trans forward⟩

/-- Memory frames can preserve the link across key copying, value updates,
header stores and local scopes without assuming the whole memory is equal. -/
theorem HashOrderLinked.framed {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items : BitVec 64)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (occupiedBefore : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot ≠ some 0 → hashOccupancyRead state used slot ≠ some 0)
    (reverseFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8))
    (forwardFrame : ∀ position : BitVec 64, position.toNat < items.toNat →
      post.memory (order + position * 8) = state.memory (order + position * 8)) :
    HashOrderLinked used order orderPos capacity items post := by
  intro slot inside occupied
  obtain ⟨position,bound,reverse,forward⟩ := linked slot inside (occupiedBefore slot inside occupied)
  exact ⟨position,bound,(reverseFrame slot inside).trans reverse,(forwardFrame position bound).trans forward⟩

#print axioms HashOrderLinked.insert
#print axioms HashOrderLinked.framed
end InitECandidate.Runtime
