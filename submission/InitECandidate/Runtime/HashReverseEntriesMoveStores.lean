import InitECandidate.Runtime.HashReverseEntriesUpdate
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The deletion movement's order and reverse stores preserve reverse bounds.
Separation is stated for actual aligned occupancy and reverse cells. -/
theorem HashReverseEntriesBound.move_stores {F : Type}
    (state : PanSemStateFiniteExact 64 F) (used order orderPos capacity items hole position : BitVec 64)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (positionBound : position.toNat < items.toNat)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + position * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      orderPos + slot * 8 ≠ order + position * 8 ∧
      orderPos + slot * 8 ≠ orderPos + hole * 8) :
    HashReverseEntriesBound used orderPos capacity items
      (sourceWriteWord (sourceWriteWord state (order + position * 8) hole) (orderPos + hole * 8) position) := by
  apply entries.move state _ used orderPos capacity items hole position positionBound
  · simp only [sourceWriteWord,ite_true]
  · intro slot inside
    have separate := occupancySeparate slot inside
    have first : panByteAlignHOL (used + slot) ≠ order + position * 8#64 := separate.1
    have second : panByteAlignHOL (used + slot) ≠ orderPos + hole * 8#64 := separate.2
    simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,first,second]
    rfl
  · intro slot inside different
    have separate := reverseSeparate slot inside different
    have first : orderPos + slot * 8#64 ≠ order + position * 8#64 := separate.1
    have second : orderPos + slot * 8#64 ≠ orderPos + hole * 8#64 := separate.2
    change (if orderPos + slot * 8 = orderPos + hole * 8 then .word position
      else if orderPos + slot * 8 = order + position * 8 then .word hole
      else state.memory (orderPos + slot * 8)) = state.memory (orderPos + slot * 8)
    rw [if_neg separate.2,if_neg separate.1]

#print axioms HashReverseEntriesBound.move_stores
end InitECandidate.Runtime
