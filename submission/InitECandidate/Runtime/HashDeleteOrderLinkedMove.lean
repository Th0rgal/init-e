import InitECandidate.Runtime.HashDeleteOrderLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Preserve the deletion link across a memory frame that excludes its hole. -/
theorem HashDeleteOrderLinked.framed {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole deletedPosition : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (occupiedBefore : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      hashOccupancyRead post used slot ≠ some 0 → hashOccupancyRead state used slot ≠ some 0)
    (reverseFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8))
    (forwardFrame : ∀ position : BitVec 64, position.toNat < items.toNat → position ≠ deletedPosition →
      post.memory (order + position * 8) = state.memory (order + position * 8)) :
    HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition post := by
  intro slot inside different occupied
  obtain ⟨position,bound,notDeleted,reverse,forward⟩ :=
    linked slot inside different (occupiedBefore slot inside different occupied)
  exact ⟨position,bound,notDeleted,(reverseFrame slot inside different).trans reverse,
    (forwardFrame position bound notDeleted).trans forward⟩

/-- Moving a live scan entry into the hole transfers its matching order pair;
the scan slot becomes the new excluded hole. -/
theorem HashDeleteOrderLinked.move {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole scan deletedPosition movedPosition : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (scanInside : scan.toNat < capacity.toNat) (scanDifferent : scan ≠ hole)
    (scanOccupied : hashOccupancyRead state used scan ≠ some 0)
    (scanReverse : state.memory (orderPos + scan * 8) = .word movedPosition)
    (newReverse : post.memory (orderPos + hole * 8) = .word movedPosition)
    (newForward : post.memory (order + movedPosition * 8) = .word hole)
    (occupiedBefore : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole → slot ≠ scan →
      hashOccupancyRead post used slot ≠ some 0 → hashOccupancyRead state used slot ≠ some 0)
    (reverseFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole → slot ≠ scan →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8))
    (forwardFrame : ∀ position : BitVec 64, position.toNat < items.toNat → position ≠ movedPosition →
      post.memory (order + position * 8) = state.memory (order + position * 8)) :
    HashDeleteOrderLinked used order orderPos capacity items scan deletedPosition post := by
  obtain ⟨moved,bound,notDeleted,reverse,forward⟩ := linked scan scanInside scanDifferent scanOccupied
  have same : moved = movedPosition := by
    have words := reverse.symm.trans scanReverse
    injection words
  subst moved
  intro slot inside notScan occupied
  by_cases isHole : slot = hole
  · subst slot
    exact ⟨movedPosition,bound,notDeleted,newReverse,newForward⟩
  · obtain ⟨position,positionBound,positionNotDeleted,oldReverse,oldForward⟩ :=
      linked slot inside isHole (occupiedBefore slot inside isHole notScan occupied)
    have distinct : position ≠ movedPosition := by
      intro equal
      rw [equal] at oldForward
      have words := oldForward.symm.trans forward
      have equalSlots : slot = scan := by injection words
      exact notScan equalSlots
    exact ⟨position,positionBound,positionNotDeleted,
      (reverseFrame slot inside isHole notScan).trans oldReverse,
      (forwardFrame position positionBound distinct).trans oldForward⟩

#print axioms HashDeleteOrderLinked.framed
#print axioms HashDeleteOrderLinked.move
end InitECandidate.Runtime
