import InitECandidate.Runtime.HashReverseEntriesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Appending a new slot's reverse position preserves every old occupied
slot's bound, without making any assertion about unused reverse cells. -/
theorem HashReverseEntriesBound.insert {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (used orderPos capacity items inserted : BitVec 64)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (noWrap : items.toNat + 1 < 2 ^ 64)
    (written : post.memory (orderPos + inserted * 8) = .word items)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ inserted →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot)
    (reverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ inserted →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8)) :
    HashReverseEntriesBound used orderPos capacity (items + 1) post := by
  have successor : (items + 1).toNat = items.toNat + 1 := BitVec.toNat_add_of_lt noWrap
  intro slot inside occupied
  by_cases same : slot = inserted
  · subst slot
    exact ⟨items,written,by rw [successor]; omega⟩
  · obtain ⟨position,cell,bound⟩ := entries slot inside
      (by rw [← occupancy slot inside same]; exact occupied)
    exact ⟨position,(reverse slot inside same).trans cell,by rw [successor]; omega⟩

/-- Moving an entry to the deletion hole writes an already bounded reverse
position; other occupied slots retain their reverse entries. -/
theorem HashReverseEntriesBound.move {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (used orderPos capacity items hole position : BitVec 64)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (positionBound : position.toNat < items.toNat)
    (written : post.memory (orderPos + hole * 8) = .word position)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot)
    (reverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8)) :
    HashReverseEntriesBound used orderPos capacity items post := by
  intro slot inside occupied
  by_cases same : slot = hole
  · subst slot
    exact ⟨position,written,positionBound⟩
  · obtain ⟨previous,cell,bound⟩ := entries slot inside
      (by rw [← occupancy slot inside]; exact occupied)
    exact ⟨previous,(reverse slot inside same).trans cell,bound⟩

#print axioms HashReverseEntriesBound.insert
#print axioms HashReverseEntriesBound.move
end InitECandidate.Runtime
