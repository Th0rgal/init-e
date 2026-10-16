import InitECandidate.Runtime.HashOrderEntriesMove
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashOrderEntriesBound.after_word {F : Type}
    (state : PanSemStateFiniteExact 64 F) (order capacity items destination value : BitVec 64)
    (entries : HashOrderEntriesBound order capacity items state)
    (separate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ destination) :
    HashOrderEntriesBound order capacity items (sourceWriteWord state destination value) := by
  intro index inside
  obtain ⟨slot,cell,bound⟩ := entries index inside
  refine ⟨slot,?_,bound⟩
  change (if order + index * 8 = destination then .word value
    else state.memory (order + index * 8)) = .word slot
  rw [if_neg (separate index inside)]
  exact cell

theorem HashOrderEntriesBound.value_move_stores {F : Type}
    (state : PanSemStateFiniteExact 64 F) (values order orderPos capacity items position hole value : BitVec 64)
    (entries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (valueSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ values + hole * 8)
    (separate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ orderPos + hole * 8)
    (positionSeparate : order + position * 8 ≠ orderPos + hole * 8)
    (distinct : ∀ index : BitVec 64, index.toNat < items.toNat → index ≠ position →
      order + index * 8 ≠ order + position * 8) :
    HashOrderEntriesBound order capacity items
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
        (order + position * 8) hole) (orderPos + hole * 8) position) := by
  have written := entries.after_word state order capacity items (values + hole * 8) value valueSeparate
  exact written.move_stores _ order orderPos capacity items position hole holeInside separate positionSeparate distinct

#print axioms HashOrderEntriesBound.after_word
#print axioms HashOrderEntriesBound.value_move_stores
end InitECandidate.Runtime
