import InitECandidate.Runtime.HashDeleteCountTail
import InitECandidate.Runtime.JournalRecordStoreFrames
import InitECandidate.Runtime.JournalUndoRecordsRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Count-loading scopes and final deletion writes preserve a disjoint table. -/
theorem evaluate_hashDelete_count_tail_record_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (orderSeparate : order.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + journalCount * 32 ≤ order.toNat)
    (reverseSeparate : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + journalCount * 32 ≤ orderPos.toNat)
    (countOutside : (table + 24).toNat < journal.toNat ∨ journal.toNat + journalCount * 32 ≤ (table + 24).toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteCountTail =
        (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  classical
  obtain ⟨post,run,clock,globals,code,domain,endian,memory,_⟩ :=
    evaluate_hashDelete_count_tail state table order orderPos deletedPosition count lastSlot
      tableLocal orderLocal reverseLocal deletedLocal countDomain countCell loadDomain loadCell orderDomain reverseDomain
  let swapped := if deletedPosition = count - 1 then state else
    sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot) (orderPos + lastSlot * 8) deletedPosition
  have swappedFrame : ∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
      swapped.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) := by
    intro index inside offset member
    unfold swapped
    split
    · rfl
    · have first := journal_record_array_word_frame state journal order capacity deletedPosition lastSlot journalCount journalBound deletedInside orderAligned orderBound orderSeparate
      have second := journal_record_array_word_frame (sourceWriteWord state (order + deletedPosition * 8) lastSlot) journal orderPos capacity lastSlot deletedPosition journalCount journalBound lastInside reverseAligned reverseBound reverseSeparate
      exact (second index inside offset member).trans (first index inside offset member)
  have written := journal_record_word_frame swapped journal (table + 24) (count - 1) journalCount journalBound countOutside
  refine ⟨post,run,?_,clock,globals,code,domain,endian⟩
  intro index inside offset member
  exact (congrFun memory _).trans ((written index inside offset member).trans (swappedFrame index inside offset member))

#print axioms evaluate_hashDelete_count_tail_record_frame
end InitECandidate.Runtime
