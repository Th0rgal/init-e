import InitECandidate.Runtime.HashOrderEntriesAppend
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Replacing an order entry by an in-range hole retains bounded entries. -/
theorem HashOrderEntriesBound.replace {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (order capacity items position hole : BitVec 64)
    (entries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (written : post.memory (order + position * 8) = .word hole)
    (frame : ∀ index : BitVec 64, index.toNat < items.toNat → index ≠ position →
      post.memory (order + index * 8) = state.memory (order + index * 8)) :
    HashOrderEntriesBound order capacity items post := by
  intro index inside
  by_cases same : index = position
  · subst index
    exact ⟨hole,written,holeInside⟩
  · obtain ⟨slot,cell,bound⟩ := entries index inside
    exact ⟨slot,(frame index inside same).trans cell,bound⟩

/-- The concrete movement order/reverse writes retain forward entry bounds. -/
theorem HashOrderEntriesBound.move_stores {F : Type}
    (state : PanSemStateFiniteExact 64 F) (order orderPos capacity items position hole : BitVec 64)
    (entries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (separate : ∀ index : BitVec 64, index.toNat < items.toNat →
      order + index * 8 ≠ orderPos + hole * 8)
    (positionSeparate : order + position * 8 ≠ orderPos + hole * 8)
    (distinct : ∀ index : BitVec 64, index.toNat < items.toNat → index ≠ position →
      order + index * 8 ≠ order + position * 8) :
    HashOrderEntriesBound order capacity items
      (sourceWriteWord (sourceWriteWord state (order + position * 8) hole) (orderPos + hole * 8) position) := by
  apply entries.replace state _ order capacity items position hole holeInside
  · change (if order + position * 8 = orderPos + hole * 8 then .word position
      else if order + position * 8 = order + position * 8 then .word hole
      else state.memory (order + position * 8)) = .word hole
    rw [if_neg positionSeparate,if_pos rfl]
  · intro index inside different
    change (if order + index * 8 = orderPos + hole * 8 then .word position
      else if order + index * 8 = order + position * 8 then .word hole
      else state.memory (order + index * 8)) = state.memory (order + index * 8)
    rw [if_neg (separate index inside),if_neg (distinct index inside different)]

#print axioms HashOrderEntriesBound.replace
#print axioms HashOrderEntriesBound.move_stores
end InitECandidate.Runtime
