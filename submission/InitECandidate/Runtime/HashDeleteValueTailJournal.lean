import InitECandidate.Runtime.HashDeleteValueTail
import InitECandidate.Runtime.HashDeleteFinalStoresJournal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion value and order movement preserves disjoint ready tables. -/
theorem evaluate_hashDelete_value_tail_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (ready : JournalUndoRecords journal count state)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (valuesSeparate : values.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ values.toNat)
    (orderSeparate : order.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ order.toNat)
    (reverseSeparate : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ orderPos.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteValueTail = (none,post) ∧
      JournalUndoRecords journal count post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have first := ready.after_array_word state values capacity hole value journalBound
    holeInside valuesAligned valuesBound valuesSeparate
  let written := sourceWriteWord state (values + hole * 8) value
  let entered := setVarHOLFinite (ofString "moved_pos") (.val (.word position)) written
  have enteredReady := first.after_frame (after := entered) (Nat.le_refl _) rfl (by intro index inside offset member; rfl)
  have second := enteredReady.after_array_word entered order capacity position hole journalBound
    positionInside orderAligned orderBound orderSeparate
  have third := second.after_array_word _ orderPos capacity hole position journalBound
    holeInside reverseAligned reverseBound reverseSeparate
  exact ⟨_,evaluate_hashDelete_value_tail state values order orderPos hole scan position value
    valuesLocal orderLocal reverseLocal holeLocal scanLocal valueDomain valueCell destinationDomain loadDomain loadCell separate orderDomain reverseDomain,
    third.after_frame (after := _) (Nat.le_refl _) rfl (by intro index inside offset member; rfl),
    rfl,rfl,rfl,rfl,rfl⟩

#print axioms evaluate_hashDelete_value_tail_journal
end InitECandidate.Runtime
