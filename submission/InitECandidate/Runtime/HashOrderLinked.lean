import InitECandidate.Runtime.HashDeleteOrderLinked
import InitECandidate.Runtime.HashEmptyEntryInvariants
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every occupied live slot is identified by its bounded reverse position
and the corresponding forward order cell. -/
def HashOrderLinked {F : Type} (used order orderPos capacity items : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead state used slot ≠ some 0 →
    ∃ position : BitVec 64, position.toNat < items.toNat ∧
      state.memory (orderPos + slot * 8) = .word position ∧
      state.memory (order + position * 8) = .word slot

theorem HashOrderLinked.empty {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity : BitVec 64)
    (zero : hashOccupiedCount capacity (hashOccupancyRead state used) = 0) :
    HashOrderLinked used order orderPos capacity 0 state := by
  intro slot inside occupied
  exact False.elim (occupied (hashOccupiedCount_zero_reads capacity (hashOccupancyRead state used) zero slot inside))

theorem HashOrderLinked.after_read {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items : BitVec 64)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (memory : post.memory = state.memory) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashOrderLinked used order orderPos capacity items post := by
  have reads : hashOccupancyRead post used = hashOccupancyRead state used := by
    funext slot
    unfold hashOccupancyRead
    rw [memory,domain,endian]
  intro slot inside occupied
  obtain ⟨position,bound,reverse,forward⟩ := linked slot inside (by rw [← reads]; exact occupied)
  exact ⟨position,bound,by rw [memory]; exact reverse,by rw [memory]; exact forward⟩

/-- Saving the hole's reverse position establishes the deletion-specific
link: no other occupied slot can claim the position being removed. -/
theorem HashOrderLinked.delete_hole {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole deletedPosition : BitVec 64)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (inside : hole.toNat < capacity.toNat) (occupied : hashOccupancyRead state used hole ≠ some 0)
    (saved : state.memory (orderPos + hole * 8) = .word deletedPosition) :
    deletedPosition.toNat < items.toNat ∧
      HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state := by
  obtain ⟨actual,bound,cell,holeForward⟩ := linked hole inside occupied
  have equal : actual = deletedPosition := by have words := cell.symm.trans saved; injection words
  rw [equal] at bound holeForward
  refine ⟨bound,?_⟩
  intro slot slotInside different slotOccupied
  obtain ⟨position,positionBound,reverse,forward⟩ := linked slot slotInside slotOccupied
  refine ⟨position,positionBound,?_,reverse,forward⟩
  intro same
  rw [same] at forward
  have words := forward.symm.trans holeForward
  have identical : slot = hole := by injection words
  exact different identical

#print axioms HashOrderLinked.empty
#print axioms HashOrderLinked.after_read
#print axioms HashOrderLinked.delete_hole
end InitECandidate.Runtime
