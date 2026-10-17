import InitECandidate.Runtime.HashDeleteValueTail
import InitECandidate.Runtime.JournalRecordStoreFrames
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion value and order movement preserves disjoint ready tables. -/
theorem evaluate_hashDelete_value_tail_record_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (values order orderPos hole scan position value : BitVec 64)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (valueDomain : state.memaddrs (values + scan * 8))
    (valueCell : state.memory (values + scan * 8) = .word value)
    (destinationDomain : state.memaddrs (values + hole * 8))
    (loadDomain : state.memaddrs (orderPos + scan * 8))
    (loadCell : state.memory (orderPos + scan * 8) = .word position)
    (separate : orderPos + scan * 8 ≠ values + hole * 8)
    (orderDomain : state.memaddrs (order + position * 8))
    (reverseDomain : state.memaddrs (orderPos + hole * 8))
    (capacity : BitVec 64)
    (holeInside : hole.toNat < capacity.toNat) (positionInside : position.toNat < capacity.toNat)
    (valuesAligned : values.toNat % 8 = 0) (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (valuesBound : values.toNat + capacity.toNat * 8 ≤ 33806089496)
    (orderBound : order.toNat + capacity.toNat * 8 ≤ 33806089496)
    (reverseBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (journal : BitVec 64) (count : Nat)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (valuesSeparate : values.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ values.toNat)
    (orderSeparate : order.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ order.toNat)
    (reverseSeparate : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ orderPos.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteValueTail = (none,post) ∧
      (∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have first := journal_record_array_word_frame state journal values capacity hole value count journalBound
    holeInside valuesAligned valuesBound valuesSeparate
  let written := sourceWriteWord state (values + hole * 8) value
  let entered := setVarHOLFinite (ofString "moved_pos") (.val (.word position)) written
  have second := journal_record_array_word_frame entered journal order capacity position hole count journalBound
    positionInside orderAligned orderBound orderSeparate
  have third := journal_record_array_word_frame (sourceWriteWord entered (order + position * 8) hole) journal orderPos capacity hole position count journalBound
    holeInside reverseAligned reverseBound reverseSeparate
  exact ⟨_,evaluate_hashDelete_value_tail state values order orderPos hole scan position value
    valuesLocal orderLocal reverseLocal holeLocal scanLocal valueDomain valueCell destinationDomain loadDomain loadCell separate orderDomain reverseDomain,
    (by
      intro index inside offset member
      exact (third index inside offset member).trans ((second index inside offset member).trans (first index inside offset member))),
    rfl,rfl,rfl,rfl,rfl⟩

#print axioms evaluate_hashDelete_value_tail_record_frame
end InitECandidate.Runtime
