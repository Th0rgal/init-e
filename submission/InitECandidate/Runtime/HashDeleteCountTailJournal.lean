import InitECandidate.Runtime.HashDeleteCountTail
import InitECandidate.Runtime.HashDeleteFinalStoresJournal
import InitECandidate.Runtime.JournalUndoRecordsRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Count-loading scopes and final deletion writes preserve a disjoint table. -/
theorem evaluate_hashDelete_count_tail_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition count lastSlot : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (countDomain : state.memaddrs (table + 24))
    (countCell : state.memory (table + 24) = .word count)
    (loadDomain : state.memaddrs (order + (count - 1) * 8))
    (loadCell : state.memory (order + (count - 1) * 8) = .word lastSlot)
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8))
    (capacity : BitVec 64)
    (deletedInside : deletedPosition.toNat < capacity.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (orderBound : order.toNat + capacity.toNat * 8 ≤ 33806089496)
    (reverseBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (journal : BitVec 64) (journalCount : Nat)
    (ready : JournalUndoRecords journal journalCount state)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (orderSeparate : order.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + journalCount * 32 ≤ order.toNat)
    (reverseSeparate : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + journalCount * 32 ≤ orderPos.toNat)
    (countOutside : (table + 24).toNat < journal.toNat ∨ journal.toNat + journalCount * 32 ≤ (table + 24).toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteCountTail =
        (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      JournalUndoRecords journal journalCount post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  classical
  obtain ⟨post,run,clock,globals,code,domain,endian,memory,_⟩ :=
    evaluate_hashDelete_count_tail state table order orderPos deletedPosition count lastSlot
      tableLocal orderLocal reverseLocal deletedLocal countDomain countCell loadDomain loadCell orderDomain reverseDomain
  let swapped := if deletedPosition = count - 1 then state else
    sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot) (orderPos + lastSlot * 8) deletedPosition
  have preserved : JournalUndoRecords journal journalCount swapped := by
    unfold swapped
    split
    · exact ready
    · have first := ready.after_array_word state order capacity deletedPosition lastSlot journalBound
        deletedInside orderAligned orderBound orderSeparate
      exact first.after_array_word _ orderPos capacity lastSlot deletedPosition journalBound
        lastInside reverseAligned reverseBound reverseSeparate
  have written := preserved.after_word_interval swapped (table + 24) (count - 1) journalBound countOutside
  have swappedGlobals : swapped.globals = state.globals := by unfold swapped; split <;> rfl
  have swappedCode : swapped.code = state.code := by unfold swapped; split <;> rfl
  have swappedDomain : swapped.memaddrs = state.memaddrs := by unfold swapped; split <;> rfl
  have swappedEndian : swapped.be = state.be := by unfold swapped; split <;> rfl
  refine ⟨post,run,?_,clock,globals,code,domain,endian⟩
  exact written.after_read _ post journal journalCount memory (domain.trans swappedDomain.symm)

#print axioms evaluate_hashDelete_count_tail_journal
end InitECandidate.Runtime
