import InitECandidate.Runtime.HashReverseEntriesMoveStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A word write outside occupancy and reverse arrays preserves every
occupied slot's bounded reverse position. -/
theorem HashReverseEntriesBound.after_word {F : Type}
    (state : PanSemStateFiniteExact 64 F) (used orderPos capacity items destination value : BitVec 64)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ destination)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ destination) :
    HashReverseEntriesBound used orderPos capacity items (sourceWriteWord state destination value) := by
  apply entries.framed state _ used orderPos capacity items
  · intro slot inside
    simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,occupancySeparate slot inside]
    rfl
  · intro slot inside
    change (if orderPos + slot * 8 = destination then .word value
      else state.memory (orderPos + slot * 8)) = state.memory (orderPos + slot * 8)
    rw [if_neg (reverseSeparate slot inside)]

/-- All three word stores in the movement tail preserve reverse bounds. -/
theorem HashReverseEntriesBound.value_move_stores {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items values hole position value : BitVec 64)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (positionBound : position.toNat < items.toNat)
    (valueOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + hole * 8)
    (valueReverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ values + hole * 8)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + position * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      orderPos + slot * 8 ≠ order + position * 8 ∧
      orderPos + slot * 8 ≠ orderPos + hole * 8) :
    HashReverseEntriesBound used orderPos capacity items
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
        (order + position * 8) hole) (orderPos + hole * 8) position) := by
  have written := entries.after_word state used orderPos capacity items (values + hole * 8) value
    valueOccupancy valueReverse
  exact written.move_stores _ used order orderPos capacity items hole position positionBound
    occupancySeparate reverseSeparate

#print axioms HashReverseEntriesBound.after_word
#print axioms HashReverseEntriesBound.value_move_stores
end InitECandidate.Runtime
