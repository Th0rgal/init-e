import InitECandidate.Runtime.JournalUndoRecordIntervals
import InitECandidate.Runtime.HashDeleteFinalStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem JournalUndoRecords.after_array_word {F : Type} {journal : BitVec 64} {count : Nat}
    (state : PanSemStateFiniteExact 64 F) (base length index value : BitVec 64)
    (valid : JournalUndoRecords journal count state)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat * 8 ≤ 33806089496)
    (separate : base.toNat + length.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ base.toNat) :
    JournalUndoRecords journal count (sourceWriteWord state (base + index * 8) value) := by
  have address := (hashFind_slot_address base index 8 length inside (by simpa using bounded) aligned (by decide)).1
  change (base + index * 8).toNat = base.toNat + index.toNat * 8 at address
  have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
  apply valid.after_word_interval state (base + index * 8) value journalBound
  rcases separate with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Original final swap, count store and return preserve disjoint ready tables. -/
theorem evaluate_hashDelete_final_stores_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition lastPosition lastSlot : BitVec 64)
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (lastLocal : state.locals.lookup (ofString "last_pos") = some (.val (.word lastPosition)))
    (loadDomain : state.memaddrs (order + lastPosition * 8))
    (loadCell : state.memory (order + lastPosition * 8) = .word lastSlot)
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (countDomain : state.memaddrs (table + 24))
    (capacity : BitVec 64)
    (deletedInside : deletedPosition.toNat < capacity.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (orderBound : order.toNat + capacity.toNat * 8 ≤ 33806089496)
    (reverseBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (journal : BitVec 64) (count : Nat)
    (ready : JournalUndoRecords journal count state)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (orderSeparate : order.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ order.toNat)
    (reverseSeparate : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ orderPos.toNat)
    (countOutside : (table + 24).toNat < journal.toNat ∨ journal.toNat + count * 32 ≤ (table + 24).toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteFinalStores =
        (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      JournalUndoRecords journal count post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  classical
  let swapped := if deletedPosition = lastPosition then state else
    sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot) (orderPos + lastSlot * 8) deletedPosition
  have preserved : JournalUndoRecords journal count swapped := by
    unfold swapped
    split
    · exact ready
    · have first := ready.after_array_word state order capacity deletedPosition lastSlot journalBound
        deletedInside orderAligned orderBound orderSeparate
      exact first.after_array_word _ orderPos capacity lastSlot deletedPosition journalBound
        lastInside reverseAligned reverseBound reverseSeparate
  have written := preserved.after_word_interval swapped (table + 24) lastPosition journalBound countOutside
  have clock : swapped.clock = state.clock := by unfold swapped; split <;> rfl
  have globals : swapped.globals = state.globals := by unfold swapped; split <;> rfl
  have code : swapped.code = state.code := by unfold swapped; split <;> rfl
  have domain : swapped.memaddrs = state.memaddrs := by unfold swapped; split <;> rfl
  have endian : swapped.be = state.be := by unfold swapped; split <;> rfl
  exact ⟨_,evaluate_hashDelete_final_stores state table order orderPos deletedPosition lastPosition lastSlot
    orderLocal reverseLocal deletedLocal lastLocal loadDomain loadCell orderDomain reverseDomain tableLocal countDomain,
    written.after_frame (after := emptyLocalsHOLFinite (sourceWriteWord swapped (table + 24) lastPosition)) (Nat.le_refl _) rfl (by intro index inside offset member; rfl),
    clock,globals,code,domain,endian⟩

#print axioms evaluate_hashDelete_final_stores_journal
end InitECandidate.Runtime
