import InitECandidate.Runtime.HashDeleteScanTailJournalSupported
import InitECandidate.Runtime.HashOrderLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The count invariant supplies the stable empty witness; the source scan
starts at the deletion hole before its first increment. -/
theorem HashTableArraysInvariant.delete_scan_tail_with_journal_from_hole_supported {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (holeInside : hole.toNat < capacity.toNat)
    (holeOccupied : hashOccupancyRead state used hole ≠ some 0)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (linked : HashOrderLinked used order orderPos capacity items state)
    (deletedPosition : BitVec 64)
    (saved : state.memory (orderPos + hole * 8) = .word deletedPosition)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (journal : BitVec 64) (journalCount : Nat)
    (otherReady : JournalUndoRecords journal journalCount state)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨
      journal.toNat + journalCount * 32 ≤ table.toNat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState (setVarHOLFinite (ofString "j") (.val (.word hole)) state)
        (.seq hashDeleteLoop hashDeleteFinalTail) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      JournalUndoRecords journal journalCount post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used)
    (by rw [← invariant.agreement]; exact invariant.room)
  let entered := setVarHOLFinite (ofString "j") (.val (.word hole)) state
  have other : ∀ name, name ≠ ofString "j" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have j : entered.locals.lookup (ofString "j") = some (.val (.word hole)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ready : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits entered := {
    arrays := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
    valuesWord := entries.after_read state entered used values capacity rfl rfl rfl
    reverse := reverse.after_read state entered used orderPos capacity items rfl rfl rfl
    ordered := ordered.after_memory state entered order capacity items rfl
    keyValueOrder := keyValueOrder
    emptyInside := emptyInside
    emptyRead := emptyRead
    keysLocal := ((other _ (by decide))).trans keysLocal
    strideLocal := ((other _ (by decide))).trans strideLocal
    sizeLocal := ((other _ (by decide))).trans sizeLocal
    capacityLocal := ((other _ (by decide))).trans capacityLocal
    usedLocal := ((other _ (by decide))).trans usedLocal
    valuesLocal := ((other _ (by decide))).trans valuesLocal
    orderLocal := ((other _ (by decide))).trans orderLocal
    reverseLocal := ((other _ (by decide))).trans reverseLocal
    indices := ⟨hole,hole,holeInside,holeInside,((other _ (by decide))).trans holeLocal,j,holeOccupied⟩
  }
  have initialLinked := (linked.delete_hole state used order orderPos capacity items hole deletedPosition holeInside holeOccupied saved).2
  have enteredLinked := initialLinked.after_read state entered used order orderPos capacity items hole deletedPosition rfl rfl rfl
  have linkedReady := HashDeleteLinkedLoopInvariantWidth.of_indices keyLength table keys stride capacity used values order orderPos items empty deletedPosition hole hole bits entered
    ready ((other _ (by decide)).trans holeLocal) j enteredLinked (HashDeleteScanOrder.initial _ _ _)
  have deletedBound := (linked.delete_hole state used order orderPos capacity items hole deletedPosition holeInside holeOccupied saved).1
  have enteredOther := otherReady.after_read state entered journal journalCount rfl rfl
  exact evaluate_hashDelete_scan_tail_journal_supported keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits entered linkedReady supported budget deletedBound
    ((other _ (by decide)).trans tableLocal) ((other _ (by decide)).trans deletedLocal)
    journal journalCount enteredOther journalBound separated

#print axioms HashTableArraysInvariant.delete_scan_tail_with_journal_from_hole_supported
end InitECandidate.Runtime
