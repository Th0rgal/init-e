import InitECandidate.Runtime.HashDeleteFinalLinkedStores
import InitECandidate.Runtime.HashDeleteFinalOrderGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Final swap writes keep each remaining forward entry within the table. -/
theorem HashOrderEntriesBound.delete_final_writes {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos capacity items deletedPosition lastSlot : BitVec 64)
    (entries : HashOrderEntriesBound order capacity items state)
    (positive : 0 < items.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (forwardSeparate : ∀ position : BitVec 64, position.toNat < items.toNat →
      order + position * 8 ≠ table + 24 ∧ order + position * 8 ≠ orderPos + lastSlot * 8 ∧
      (position ≠ deletedPosition → order + position * 8 ≠ order + deletedPosition * 8)) :
    HashOrderEntriesBound order capacity (items - 1)
      (sourceWriteWord
        (if deletedPosition = items - 1 then state else
          sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
            (orderPos + lastSlot * 8) deletedPosition) (table + 24) (items - 1)) := by
  have subtraction : (items - (1 : BitVec 64)).toNat = items.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ items.toNat; omega))]
    rfl
  intro position inside
  have oldInside : position.toNat < items.toNat := by omega
  have separates := forwardSeparate position oldInside
  classical
  by_cases noSwap : deletedPosition = items - 1
  · simp only [if_pos noSwap]
    obtain ⟨slot,cell,bound⟩ := entries position oldInside
    refine ⟨slot,?_,bound⟩
    change (if order + position * 8 = table + 24 then HolWordLab.word (items - 1) else _) = _
    rw [if_neg separates.1]
    exact cell
  · simp only [if_neg noSwap]
    by_cases isDeleted : position = deletedPosition
    · subst position
      refine ⟨lastSlot,?_,lastInside⟩
      change (if order + deletedPosition * 8 = table + 24 then HolWordLab.word (items - 1) else _) = _
      rw [if_neg separates.1]
      change (if order + deletedPosition * 8 = orderPos + lastSlot * 8 then HolWordLab.word deletedPosition else _) = _
      rw [if_neg separates.2.1]
      simp [sourceWriteWord]
    · obtain ⟨slot,cell,bound⟩ := entries position oldInside
      refine ⟨slot,?_,bound⟩
      change (if order + position * 8 = table + 24 then HolWordLab.word (items - 1) else _) = _
      rw [if_neg separates.1]
      change (if order + position * 8 = orderPos + lastSlot * 8 then HolWordLab.word deletedPosition else _) = _
      rw [if_neg separates.2.1]
      change (if order + position * 8 = order + deletedPosition * 8 then HolWordLab.word lastSlot else _) = _
      rw [if_neg (separates.2.2 isDeleted)]
      exact cell

theorem HashOrderEntriesBound.delete_final_writes_layout32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items deletedPosition lastSlot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashOrderEntriesBound order capacity items state)
    (positive : 0 < items.toNat) (deletedInside : deletedPosition.toNat < items.toNat)
    (lastInside : lastSlot.toNat < capacity.toNat) :
    HashOrderEntriesBound order capacity (items - 1)
      (sourceWriteWord
        (if deletedPosition = items - 1 then state else
          sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
            (orderPos + lastSlot * 8) deletedPosition) (table + 24) (items - 1)) := by
  obtain ⟨newForward,forward⟩ := invariant.delete_final_order_separation state table keys stride capacity used values order orderPos items deletedPosition lastSlot bits deletedInside lastInside
  apply entries.delete_final_writes state table order orderPos capacity items deletedPosition lastSlot positive lastInside
  intro position inside
  refine ⟨(forward position inside).1,?_,fun different => ((forward position inside).2 different).1⟩
  by_cases same : position = deletedPosition
  · subst position; exact newForward.1
  · exact ((forward position inside).2 same).2

#print axioms HashOrderEntriesBound.delete_final_writes_layout32
#print axioms HashOrderEntriesBound.delete_final_writes
end InitECandidate.Runtime
