import InitECandidate.Runtime.HashDeleteOrderLinkedMove
import InitECandidate.Runtime.HashOrderLinkedWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The three concrete word stores in deletion transfer linkage to the new hole. -/
theorem HashDeleteOrderLinked.move_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole scan deletedPosition position value values : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (inside : scan.toNat < capacity.toNat) (different : scan ≠ hole)
    (occupied : hashOccupancyRead state used scan ≠ some 0)
    (cell : state.memory (orderPos + scan * 8) = .word position)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + hole * 8 ∧
      panByteAlignHOL (used + slot) ≠ order + position * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      orderPos + slot * 8 ≠ values + hole * 8 ∧
      orderPos + slot * 8 ≠ order + position * 8 ∧
      orderPos + slot * 8 ≠ orderPos + hole * 8)
    (forwardSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → index ≠ position →
      order + index * 8 ≠ values + hole * 8 ∧
      order + index * 8 ≠ order + position * 8 ∧
      order + index * 8 ≠ orderPos + hole * 8)
    (newSeparate : order + position * 8 ≠ orderPos + hole * 8) :
    HashDeleteOrderLinked used order orderPos capacity items scan deletedPosition
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
        (order + position * 8) hole) (orderPos + hole * 8) position) := by
  let post := sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
    (order + position * 8) hole) (orderPos + hole * 8) position
  apply linked.move state post used order orderPos capacity items hole scan deletedPosition position inside different occupied cell
  · simp [post,sourceWriteWord]
  · change (if order + position * 8 = orderPos + hole * 8 then HolWordLab.word position else _) = _
    rw [if_neg newSeparate]
    simp [sourceWriteWord]
  · intro slot bound notHole notScan live
    have separates : panByteAlignHOL (used + slot) ≠ values + hole * 8#64 ∧
        panByteAlignHOL (used + slot) ≠ order + position * 8#64 ∧
        panByteAlignHOL (used + slot) ≠ orderPos + hole * 8#64 := occupancySeparate slot bound
    have same : hashOccupancyRead post used slot = hashOccupancyRead state used slot := by
      simp [hashOccupancyRead,post,panMemLoadByteHOL,sourceWriteWord,separates.1,separates.2.1,separates.2.2]
      rfl
    rw [← same]
    exact live
  · intro slot bound notHole notScan
    have separates := reverseSeparate slot bound notHole
    change (if orderPos + slot * 8 = orderPos + hole * 8 then HolWordLab.word position else _) = _
    rw [if_neg separates.2.2]
    change (if orderPos + slot * 8 = order + position * 8 then HolWordLab.word hole else _) = _
    rw [if_neg separates.2.1]
    change (if orderPos + slot * 8 = values + hole * 8 then HolWordLab.word value else _) = _
    rw [if_neg separates.1]
  · intro index bound notPosition
    have separates := forwardSeparate index bound notPosition
    change (if order + index * 8 = orderPos + hole * 8 then HolWordLab.word position else _) = _
    rw [if_neg separates.2.2]
    change (if order + index * 8 = order + position * 8 then HolWordLab.word hole else _) = _
    rw [if_neg separates.2.1]
    change (if order + index * 8 = values + hole * 8 then HolWordLab.word value else _) = _
    rw [if_neg separates.1]

#print axioms HashDeleteOrderLinked.move_stores
end InitECandidate.Runtime
