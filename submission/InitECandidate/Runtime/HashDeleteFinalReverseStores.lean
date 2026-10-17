import InitECandidate.Runtime.HashDeleteFinalReverseBound
import InitECandidate.Runtime.HashOrderLinkedWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Concrete final swap and header writes establish the decremented reverse bound. -/
theorem HashDeleteOrderLinked.final_swap_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole deletedPosition lastSlot table : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (positive : 0 < items.toNat) (deletedBound : deletedPosition.toNat < (items - 1).toNat)
    (holeEmpty : hashOccupancyRead state used hole = some 0)
    (lastForward : state.memory (order + (items - 1) * 8) = .word lastSlot)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + deletedPosition * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + lastSlot * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ lastSlot →
      orderPos + slot * 8 ≠ order + deletedPosition * 8 ∧
      orderPos + slot * 8 ≠ orderPos + lastSlot * 8 ∧ orderPos + slot * 8 ≠ table + 24)
    (headerSeparate : orderPos + lastSlot * 8 ≠ table + 24) :
    HashReverseEntriesBound used orderPos capacity (items - 1)
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
        (orderPos + lastSlot * 8) deletedPosition) (table + 24) (items - 1)) := by
  let post := sourceWriteWord (sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
    (orderPos + lastSlot * 8) deletedPosition) (table + 24) (items - 1)
  apply linked.final_swap_reverse_bound state post used order orderPos capacity items hole deletedPosition lastSlot
    positive deletedBound lastForward
  · change (if orderPos + lastSlot * 8 = table + 24 then HolWordLab.word (items - 1) else _) = _
    rw [if_neg headerSeparate]
    simp [sourceWriteWord]
  · intro slot inside occupied
    have separates : panByteAlignHOL (used + slot) ≠ order + deletedPosition * 8#64 ∧
        panByteAlignHOL (used + slot) ≠ orderPos + lastSlot * 8#64 ∧
        panByteAlignHOL (used + slot) ≠ table + 24#64 := occupancySeparate slot inside
    have same : hashOccupancyRead post used slot = hashOccupancyRead state used slot := by
      simp [hashOccupancyRead,post,panMemLoadByteHOL,sourceWriteWord,separates.1,separates.2.1,separates.2.2]
      rfl
    have before : hashOccupancyRead state used slot ≠ some 0 := by rw [← same]; exact occupied
    refine ⟨?_,before⟩
    intro equal
    subst slot
    exact before holeEmpty
  · intro slot inside different
    have separates := reverseSeparate slot inside different
    change (if orderPos + slot * 8 = table + 24 then HolWordLab.word (items - 1) else _) = _
    rw [if_neg separates.2.2]
    change (if orderPos + slot * 8 = orderPos + lastSlot * 8 then HolWordLab.word deletedPosition else _) = _
    rw [if_neg separates.2.1]
    change (if orderPos + slot * 8 = order + deletedPosition * 8 then HolWordLab.word lastSlot else _) = _
    rw [if_neg separates.1]

#print axioms HashDeleteOrderLinked.final_swap_stores
end InitECandidate.Runtime
