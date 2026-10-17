import InitECandidate.Runtime.StateRestoreRecordLoadScopes
import InitECandidate.Runtime.StateRestoreRecordDecisionPreservesJournal
import InitECandidate.Runtime.JournalRecordGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Bound the complete record application in the frozen rollback source. -/
theorem HashTableReady.restore_record_application_preserves_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count present value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 ^ 72 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (tableDomain : state.memaddrs (journal + count * 32))
    (tableCell : state.memory (journal + count * 32) = .word table)
    (keyDomain : state.memaddrs (journal + count * 32 + 8))
    (keyCell : state.memory (journal + count * 32 + 8) = .word key)
    (presentDomain : state.memaddrs (journal + count * 32 + 16)) (presentCell : state.memory (journal + count * 32 + 16) = .word present)
    (valueDomain : state.memaddrs (journal + count * 32 + 24)) (valueCell : state.memory (journal + count * 32 + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journalCount : Nat)
    (journalReady : JournalUndoRecords journal journalCount state)
    (journalBeforeTable : journal.toNat + journalCount * 32 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state stateRestoreApplyRecord = (none,post) ∧
      (∃ nextPointer nextKeys nextCapacity nextUsed nextValues nextOrder nextOrderPos nextItems nextBits,
        HashTableReady keyLength table nextKeys stride nextCapacity nextUsed nextValues nextOrder nextOrderPos nextItems nextBits nextPointer post) ∧
      JournalUndoRecords journal journalCount post ∧
      stateRestoreRank post = stateRestoreRank state ∧
      state.clock ≤ post.clock + 2 ^ 72 ∧ post.clock ≤ state.clock := by
  let record := journal + count * 32
  let recordState := setVarHOLFinite (ofString "r") (.val (.word record)) state
  let tableState := setVarHOLFinite (ofString "t") (.val (.word table)) recordState
  let entry := setVarHOLFinite (ofString "key") (.val (.word key)) tableState
  have entryReady := ready.after_read state entry keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have distinctRK : ofString "key" ≠ ofString "r" := by decide
  have distinctRT : ofString "t" ≠ ofString "r" := by decide
  have distinctTK : ofString "key" ≠ ofString "t" := by decide
  obtain ⟨bodyPost,decision,⟨np,nk,nc,nu,nv,no,nop,ni,nb,postReady⟩,journalPost,rank,cost,remaining⟩ := entryReady.restore_record_decision_preserves_journal entry keyLength table pointer keys stride capacity used values order orderPos items key record present value bits supported strideBound capacityLarge safePlan ticks domain
    (by simp [entry,tableState,setVarHOLFinite,FUPDATE,distinctTK])
    (by simp [entry,setVarHOLFinite,FUPDATE])
    (by simp [entry,tableState,recordState,setVarHOLFinite,FUPDATE,distinctRK,distinctRT])
    presentDomain presentCell valueDomain valueCell keyAligned keyWords keyBytes
    journal journalCount (journalReady.after_read state entry journal journalCount rfl rfl) journalBeforeTable
  let restoreKey := {bodyPost with locals := HolFiniteMapExact.resVarEq bodyPost.locals (ofString "key",recordState.locals.lookup (ofString "key"))}
  let restoreTable := {restoreKey with locals := HolFiniteMapExact.resVarEq restoreKey.locals (ofString "t",recordState.locals.lookup (ofString "t"))}
  let post := {restoreTable with locals := HolFiniteMapExact.resVarEq restoreTable.locals (ofString "r",state.locals.lookup (ofString "r"))}
  refine ⟨post,?_,⟨np,nk,nc,nu,nv,no,nop,ni,nb,postReady.after_read bodyPost post keyLength table nk stride nc nu nv no nop ni nb np rfl rfl rfl rfl rfl⟩,journalPost.after_read bodyPost post journal journalCount rfl rfl,?_,cost,remaining⟩
  · rw [stateRestore_apply_record_shape,evaluate_journal_record_scope32 state journal count _ journalGlobal countGlobal]
    rw [evaluate_stateRestore_record_loads recordState record table key (by simp [recordState,setVarHOLFinite,FUPDATE]) tableDomain tableCell keyDomain keyCell]
    rw [decision]
  · have one := stateRestoreRank_restore_local bodyPost (ofString "key") (recordState.locals.lookup (ofString "key")) (by decide)
    have two := stateRestoreRank_restore_local restoreKey (ofString "t") (recordState.locals.lookup (ofString "t")) (by decide)
    have three := stateRestoreRank_restore_local restoreTable (ofString "r") (state.locals.lookup (ofString "r")) (by decide)
    have entryRank : stateRestoreRank entry = stateRestoreRank state := by
      have a : ofString "key" ≠ ofString "snap" := by decide
      have b : ofString "t" ≠ ofString "snap" := by decide
      have c : ofString "r" ≠ ofString "snap" := by decide
      simp [stateRestoreRank,entry,tableState,recordState,setVarHOLFinite,FUPDATE,a,b,c]
    exact three.trans (two.trans (one.trans (rank.trans entryRank)))

#print axioms HashTableReady.restore_record_application_preserves_journal
end InitECandidate.Runtime
