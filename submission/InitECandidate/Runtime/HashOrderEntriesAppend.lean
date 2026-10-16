import InitECandidate.Runtime.HashOrderEntriesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Extending a live order array with an in-range slot preserves validity.
The frame premise applies only to already live entries. -/
theorem HashOrderEntriesBound.append {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (order capacity items slot : BitVec 64)
    (entries : HashOrderEntriesBound order capacity items state)
    (noWrap : items.toNat + 1 < 2 ^ 64)
    (inside : slot.toNat < capacity.toNat)
    (written : post.memory (order + items * 8) = .word slot)
    (frame : ∀ position : BitVec 64, position.toNat < items.toNat →
      post.memory (order + position * 8) = state.memory (order + position * 8)) :
    HashOrderEntriesBound order capacity (items + 1) post := by
  intro position bound
  have successor : (items + 1).toNat = items.toNat + 1 := by
    exact BitVec.toNat_add_of_lt noWrap
  rw [successor] at bound
  by_cases old : position.toNat < items.toNat
  · obtain ⟨previous,memory,valid⟩ := entries position old
    exact ⟨previous,(frame position old).trans memory,valid⟩
  · have equal : position = items := BitVec.eq_of_toNat_eq (by omega)
    subst position
    exact ⟨slot,written,inside⟩

/-- Pure reads and changes to clock, locals or globals retain order validity. -/
theorem HashOrderEntriesBound.after_memory {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (order capacity items : BitVec 64)
    (entries : HashOrderEntriesBound order capacity items state)
    (memory : post.memory = state.memory) :
    HashOrderEntriesBound order capacity items post := by
  intro position inside
  obtain ⟨slot,read,valid⟩ := entries position inside
  exact ⟨slot,by rw [memory]; exact read,valid⟩

/-- The three actual bookkeeping word stores append the chosen slot, provided
reverse-index and count cells do not overlap live order entries. -/
theorem HashOrderEntriesBound.bookkeeping {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table order orderPos capacity items slot : BitVec 64)
    (entries : HashOrderEntriesBound order capacity items state)
    (noWrap : items.toNat + 1 < 2 ^ 64)
    (inside : slot.toNat < capacity.toNat)
    (separate : ∀ position : BitVec 64, position.toNat ≤ items.toNat →
      order + position * 8 ≠ orderPos + slot * 8 ∧ order + position * 8 ≠ table + 24)
    (distinct : ∀ position : BitVec 64, position.toNat < items.toNat →
      order + position * 8 ≠ order + items * 8) :
    HashOrderEntriesBound order capacity (items + 1)
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state
        (order + items * 8) slot) (orderPos + slot * 8) items) (table + 24) (items + 1)) := by
  apply entries.append state _ order capacity items slot noWrap inside
  · have ne := separate items (by omega)
    simp only [sourceWriteWord,if_neg ne.2,if_neg ne.1,ite_true]
  · intro position old
    have ne := separate position (by omega)
    simp only [sourceWriteWord,if_neg ne.2,if_neg ne.1,if_neg (distinct position old)]

#print axioms HashOrderEntriesBound.bookkeeping
#print axioms HashOrderEntriesBound.append
#print axioms HashOrderEntriesBound.after_memory
end InitECandidate.Runtime
