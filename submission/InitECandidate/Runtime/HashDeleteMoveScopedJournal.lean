import InitECandidate.Runtime.JournalUndoRecordsRead
import InitECandidate.Runtime.HashDeleteMoveScoped32
import InitECandidate.Runtime.HashDeleteMoveAllocatedJournal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual movement scopes restore locals while preserving the other table. -/
theorem evaluate_hashDelete_move_scoped_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength keys stride hole scan values order orderPos used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (hash : BitVec 64)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (moves : hashDeleteMoveRequired hole scan (hash &&& (capacity - 1)))
    (table : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (scanInside : scan.toNat < capacity.toNat)
    (occupied : hashOccupancyRead state used scan ≠ some 0)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (budget : keyLength.toNat + 1 ≤ state.clock)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (orderEntries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (journal : BitVec 64) (count : Nat)
    (ready : JournalUndoRecords journal count state)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨
      journal.toNat + count * 32 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteAfterHash = (none,post) ∧
      JournalUndoRecords journal count post ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := hashDeleteMoveEntry state hash capacity
  have other : ∀ name, name ≠ ofString "home" → name ≠ ofString "movable" → entered.locals.lookup name = state.locals.lookup name := by
    intro name notHome notMovable
    simp [entered,hashDeleteMoveEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHome,Ne.symm notMovable]
  have enteredInvariant := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  have enteredReady := ready.after_read state entered journal count rfl rfl
  obtain ⟨post,run,preserved,cost,remaining,globals,code,domain,endian⟩ :=
    evaluate_hashDelete_move_allocated_journal entered keyLength keys stride hole scan values order orderPos used capacity items
      ((other _ (by decide) (by decide)).trans keysLocal) ((other _ (by decide) (by decide)).trans strideLocal)
      ((other _ (by decide) (by decide)).trans holeLocal) ((other _ (by decide) (by decide)).trans scanLocal)
      ((other _ (by decide) (by decide)).trans sizeLocal) table bits enteredInvariant scanInside occupied keysBeforeValues budget
      ((other _ (by decide) (by decide)).trans valuesLocal) ((other _ (by decide) (by decide)).trans orderLocal)
      ((other _ (by decide) (by decide)).trans reverseLocal)
      (entries.after_read state entered used orderPos capacity items rfl rfl rfl)
      (orderEntries.after_memory state entered order capacity items rfl) holeInside
      (valueEntries.after_read state entered used values capacity rfl rfl rfl)
      journal count enteredReady journalBound separated
  have scopeRun := evaluate_hashDelete_move_scope_run state post hole scan hash capacity holeLocal scanLocal hashLocal capacityLocal moves run
  exact ⟨hashDeleteMoveExit state post,scopeRun,
    preserved.after_read post _ journal count rfl rfl,
    cost,remaining,globals,code,domain,endian⟩

#print axioms evaluate_hashDelete_move_scoped_journal
end InitECandidate.Runtime
