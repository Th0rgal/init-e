import InitECandidate.Runtime.StateRestoreRank
import InitECandidate.Runtime.HashTableDeleteCallJournalSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Undoing a newly inserted key preserves the journal rank and complete table invariant. -/
theorem HashTableReady.restore_record_delete_preserves_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key record : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (ticks : 2 ^ 72 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (presentDomain : state.memaddrs (record + 16))
    (presentCell : state.memory (record + 16) = .word 0)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journal : BitVec 64) (journalCount : Nat)
    (journalReady : JournalUndoRecords journal journalCount state)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨ journal.toNat + journalCount * 32 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state stateRestoreRecordDecision = (none,post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits pointer post) ∧
      JournalUndoRecords journal journalCount post ∧
      stateRestoreRank post = stateRestoreRank state ∧
      state.clock ≤ post.clock + 2 ^ 72 ∧ post.clock ≤ state.clock := by
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have u := ready.live.arrays.usedBefore
    have o := ready.live.arrays.orderBefore
    have e := ready.live.arrays.endBound
    omega
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "r") 16)) = some (.val (.word (0 : BitVec 64))) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "r") record 16 r]
    simp [memLoadHOLExact]
    exact ⟨presentDomain,presentCell⟩
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
    rw [evalHOLExact,loaded]
    simp [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k]
  obtain ⟨post,run,postReady,journalPost,cost,remaining,locals,globals,_⟩ := ready.delete_call_supported_with_journal state keyLength table pointer keys stride capacity used values order orderPos items key bits supported
    _ _ args keyAligned keyWords keyBytes (by omega) journal journalCount journalReady journalBound separated
  refine ⟨post,?_,postReady,journalPost,?_,by omega,remaining⟩
  · unfold stateRestoreRecordDecision
    rw [evaluateHOLFiniteState_ite,condition]
    simpa using run
  · simp only [stateRestoreRank,locals,globals]

#print axioms HashTableReady.restore_record_delete_preserves_journal
end InitECandidate.Runtime
