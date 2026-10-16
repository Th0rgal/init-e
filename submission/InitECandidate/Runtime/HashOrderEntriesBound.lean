import InitECandidate.Runtime.HashGrowRehashBodyArraysMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every live order entry is an in-range slot of its old table. This is a
pure memory property, independent of temporary locals and evaluator behavior. -/
def HashOrderEntriesBound {F : Type} (order capacity items : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ position : BitVec 64, position.toNat < items.toNat →
    ∃ slot : BitVec 64, state.memory (order + position * 8) = .word slot ∧ slot.toNat < capacity.toNat

/-- Newly initialized empty order arrays satisfy the property vacuously. -/
theorem HashOrderEntriesBound.empty {F : Type} (order capacity : BitVec 64) (state : PanSemStateFiniteExact 64 F) :
    HashOrderEntriesBound order capacity 0 state := by
  intro position inside
  change position.toNat < 0 at inside
  omega

/-- Rehash insertion leaves every live old order entry valid when the old
order allocation lies in the protected earlier region. -/
theorem HashOrderEntriesBound.preserved {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table order capacity items : BitVec 64) (frontier : Nat)
    (entries : HashOrderEntriesBound order capacity items state)
    (orderAligned : order.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ order.toNat)
    (orderEnd : order.toNat + capacity.toNat * 8 ≤ frontier)
    (frontierBound : frontier ≤ 33806089496) (itemsBound : items.toNat ≤ capacity.toNat)
    (frame : ∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < frontier →
      post.memory watched = state.memory watched) :
    HashOrderEntriesBound order capacity items post := by
  intro position inside
  obtain ⟨slot,memory,valid⟩ := entries position inside
  have interval := hashFind_slot_offset order position 8 capacity 8 0 (by omega)
    (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
    orderAligned (by decide) (by decide) (by decide)
  have lower : order.toNat ≤ (order + position * 8).toNat := by simpa using interval.2.1
  have upper : (order + position * 8).toNat < order.toNat + capacity.toNat * 8 := by simpa using interval.2.2
  exact ⟨slot,(frame _ (by omega) (by omega)).trans memory,valid⟩

#print axioms HashOrderEntriesBound.empty
#print axioms HashOrderEntriesBound.preserved
end InitECandidate.Runtime
