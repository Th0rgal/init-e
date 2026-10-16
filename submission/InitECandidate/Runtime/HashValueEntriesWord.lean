import InitECandidate.Runtime.HashReverseEntriesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Occupied slots have word-valued cells; empty slots may remain uninitialized. -/
def HashValueEntriesWord {F : Type} (used values capacity : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
    hashOccupancyRead state used slot ≠ some 0 →
    ∃ value : BitVec 64, state.memory (values + slot * 8) = .word value

theorem HashValueEntriesWord.empty {F : Type}
    (state : PanSemStateFiniteExact 64 F) (used values capacity : BitVec 64)
    (zeroed : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead state used slot = some 0) :
    HashValueEntriesWord used values capacity state := by
  intro slot inside occupied
  exact False.elim (occupied (zeroed slot inside))

/-- Writing a word at one slot preserves value readability elsewhere, while
allowing that slot to become occupied as part of an insertion. -/
theorem HashValueEntriesWord.write_slot {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (used values capacity changed value : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (written : post.memory (values + changed * 8) = .word value)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ changed →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot)
    (frame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ changed →
      post.memory (values + slot * 8) = state.memory (values + slot * 8)) :
    HashValueEntriesWord used values capacity post := by
  intro slot inside occupied
  by_cases same : slot = changed
  · subst slot
    exact ⟨value,written⟩
  · obtain ⟨previous,cell⟩ := entries slot inside (by rw [← occupancy slot inside same]; exact occupied)
    exact ⟨previous,(frame slot inside same).trans cell⟩

theorem HashValueEntriesWord.after_read {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (used values capacity : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (memory : post.memory = state.memory) (domain : post.memaddrs = state.memaddrs)
    (endian : post.be = state.be) : HashValueEntriesWord used values capacity post := by
  have reads : hashOccupancyRead post used = hashOccupancyRead state used := by
    funext slot
    unfold hashOccupancyRead
    rw [memory,domain,endian]
  intro slot inside occupied
  obtain ⟨value,cell⟩ := entries slot inside (by rw [← reads]; exact occupied)
  exact ⟨value,by rw [memory]; exact cell⟩

#print axioms HashValueEntriesWord.empty
#print axioms HashValueEntriesWord.write_slot
#print axioms HashValueEntriesWord.after_read
end InitECandidate.Runtime
