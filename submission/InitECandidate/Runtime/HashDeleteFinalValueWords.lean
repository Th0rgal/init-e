import InitECandidate.Runtime.HashDeleteFinalCountFrame
import InitECandidate.Runtime.HashValueWordStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashValueEntriesWord.delete_final_writes {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos used values capacity items deletedPosition lastSlot : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + deletedPosition * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + lastSlot * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24)
    (valueSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + deletedPosition * 8 ∧ values + slot * 8 ≠ orderPos + lastSlot * 8 ∧ values + slot * 8 ≠ table + 24) :
    HashValueEntriesWord used values capacity
      (sourceWriteWord
        (if deletedPosition = items - 1 then state else
          sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
            (orderPos + lastSlot * 8) deletedPosition) (table + 24) (items - 1)) := by
  classical
  split
  · exact entries.after_word state used values capacity (table + 24) (items - 1)
      (fun slot inside => (occupancySeparate slot inside).2.2) (fun slot inside => (valueSeparate slot inside).2.2)
  · have first := entries.after_word state used values capacity (order + deletedPosition * 8) lastSlot
      (fun slot inside => (occupancySeparate slot inside).1) (fun slot inside => (valueSeparate slot inside).1)
    have second := first.after_word _ used values capacity (orderPos + lastSlot * 8) deletedPosition
      (fun slot inside => (occupancySeparate slot inside).2.1) (fun slot inside => (valueSeparate slot inside).2.1)
    exact second.after_word _ used values capacity (table + 24) (items - 1)
      (fun slot inside => (occupancySeparate slot inside).2.2) (fun slot inside => (valueSeparate slot inside).2.2)

#print axioms HashValueEntriesWord.delete_final_writes
end InitECandidate.Runtime
