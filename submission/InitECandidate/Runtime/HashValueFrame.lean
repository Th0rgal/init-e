import InitECandidate.Runtime.HashValueEntriesWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashValueEntriesWord.framed {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (used values capacity : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot)
    (reverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      post.memory (values + slot * 8) = state.memory (values + slot * 8)) :
    HashValueEntriesWord used values capacity post := by
  intro slot inside occupied
  obtain ⟨value,cell⟩ := entries slot inside (by rw [← occupancy slot inside]; exact occupied)
  exact ⟨value,(reverse slot inside).trans cell⟩

#print axioms HashValueEntriesWord.framed
end InitECandidate.Runtime
