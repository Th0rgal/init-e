import InitECandidate.Runtime.HashDeleteMoveArraysWidth
import InitECandidate.Runtime.HashDeleteValueTailJournal
import InitECandidate.Runtime.HashTableReadyIntervalFrame
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original key/value/order movement preserves a disjoint table. -/
theorem evaluate_hashDelete_move_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength keys stride hole scan values order orderPos position value used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (small : (keys + hole * stride).toNat + keyLength.toNat ≤ 33806089496)
    (aligned : (keys + hole * stride).toNat % 8 = 0) (scanAligned : (keys + scan * stride).toNat % 8 = 0) (budget : keyLength.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs ((keys + hole * stride) + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL ((keys + hole * stride) + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs ((keys + scan * stride) + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL ((keys + scan * stride) + BitVec.ofNat 64 offset)))
    (protectedCells : ∀ cell ∈ ([values + scan * 8,orderPos + scan * 8] : List (BitVec 64)),
      ∀ offset : Nat, offset < keyLength.toNat →
        cell ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
        cell ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (code : state.code = originalRuntimeCode)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (valueDomain : state.memaddrs (values + scan * 8))
    (valueCell : state.memory (values + scan * 8) = .word value)
    (destinationDomain : state.memaddrs (values + hole * 8))
    (loadDomain : state.memaddrs (orderPos + scan * 8))
    (loadCell : state.memory (orderPos + scan * 8) = .word position)
    (separate : orderPos + scan * 8 ≠ values + hole * 8)
    (orderDomain : state.memaddrs (order + position * 8))
    (reverseDomain : state.memaddrs (orderPos + hole * 8))
    (table : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (holeInside : hole.toNat < capacity.toNat) (positionBound : position.toNat < items.toNat)
    (journal : BitVec 64) (count : Nat)
    (ready : JournalUndoRecords journal count state)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (copyOutside : (keys + hole * stride).toNat + keyLength.toNat ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ (keys + hole * stride).toNat)
    (valuesSeparate : values.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ values.toNat)
    (orderSeparate : order.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ order.toNat)
    (reverseSeparate : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ orderPos.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveBody = (none,post) ∧
      JournalUndoRecords journal count post ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have valueProtected := protectedCells (values + scan * 8) (by simp)
  obtain ⟨copied,copyRun,_,cost,remaining,globals,postCode,addresses,endian,locals,frame⟩ :=
    evaluate_hashDelete_copy_frame state keys stride hole scan keyLength (values + scan * 8)
      keysLocal strideLocal holeLocal scanLocal sizeLocal small aligned scanAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain
      (fun offset inside => (valueProtected offset inside).1)
      (fun offset inside => (valueProtected offset inside).2) code
  have valueAfter : copied.memory (values + scan * 8) = .word value := by
    rw [frame _ (fun offset inside => (valueProtected offset inside).1)
      (fun offset inside => (valueProtected offset inside).2)]
    exact valueCell
  have reverseProtected := protectedCells (orderPos + scan * 8) (by simp)
  have positionAfter : copied.memory (orderPos + scan * 8) = .word position := by
    rw [frame _ (fun offset inside => (reverseProtected offset inside).1)
      (fun offset inside => (reverseProtected offset inside).2)]
    exact loadCell
  have copiedReady : JournalUndoRecords journal count copied := by
    apply ready.after_frame (after := copied) (Nat.le_refl _) addresses
    intro index inside offset member
    have smallOffset : offset < 32 := by simp at member; omega
    have interval := journal_undo_field_interval journal count index offset journalBound inside smallOffset
    have separation := memcpy_interval_separate (keys + hole * stride) keyLength
      (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) aligned small
      (by rcases copyOutside with before | after
          · exact Or.inr (by omega)
          · exact Or.inl (by omega))
    exact frame _ (fun offset inside => (separation offset inside).1) (fun offset inside => (separation offset inside).2)
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bound := invariant.endBound
  have room := invariant.room
  obtain ⟨post,tail,preserved,ticks,postGlobals,postCodeEq,postDomain,postEndian⟩ := evaluate_hashDelete_value_tail_journal copied values order orderPos hole scan position value
    (by rw [locals]; exact valuesLocal) (by rw [locals]; exact orderLocal)
    (by rw [locals]; exact reverseLocal) (by rw [locals]; exact holeLocal) (by rw [locals]; exact scanLocal)
    (by rw [addresses]; exact valueDomain) valueAfter (by rw [addresses]; exact destinationDomain)
    (by rw [addresses]; exact loadDomain) positionAfter separate
    (by rw [addresses]; exact orderDomain) (by rw [addresses]; exact reverseDomain)
    capacity holeInside (by omega) invariant.valuesAligned invariant.orderAligned invariant.orderPosAligned
    (by omega) (by omega) bound journal count copiedReady journalBound valuesSeparate orderSeparate reverseSeparate
  change state.clock ≤ copied.clock + keyLength.toNat + 1 at cost
  exact ⟨post,copyRun.trans tail,preserved,by omega,by omega,
    postGlobals.trans globals,postCodeEq.trans postCode,postDomain.trans addresses,postEndian.trans endian⟩

#print axioms evaluate_hashDelete_move_journal
end InitECandidate.Runtime
