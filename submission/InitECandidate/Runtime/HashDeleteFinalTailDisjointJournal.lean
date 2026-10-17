import InitECandidate.Runtime.HashDeleteFinalTailJournal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One allocation separation condition frames the complete deletion suffix. -/
theorem evaluate_hashDelete_final_tail_disjoint_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (holeInside : hole.toNat < capacity.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (positive : 0 < items.toNat) (deletedBound : deletedPosition.toNat < items.toNat)
    (cellMemory : state.memory (panByteAlignHOL (used + hole)) = .word cell)
    (lastCell : state.memory (order + (items - 1) * 8) = .word lastSlot)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (journal : BitVec 64) (journalCount : Nat)
    (otherReady : JournalUndoRecords journal journalCount state)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (separate : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨
      journal.toNat + journalCount * 32 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteFinalTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      JournalUndoRecords journal journalCount post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have countAddress : (table + 24).toNat = table.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
    rfl
  apply evaluate_hashDelete_final_tail_journal state keyLength table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell bits
    invariant holeInside lastInside positive deletedBound cellMemory lastCell tableLocal orderLocal reverseLocal deletedLocal usedLocal holeLocal
    journal journalCount otherReady journalBound
  · rcases separate with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases separate with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases separate with before | after
    · exact Or.inl before
    · exact Or.inr (by omega)
  · rcases separate with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

#print axioms evaluate_hashDelete_final_tail_disjoint_journal
end InitECandidate.Runtime
