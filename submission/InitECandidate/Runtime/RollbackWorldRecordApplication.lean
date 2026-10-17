import InitECandidate.Runtime.StateRestoreRecordLoadScopes
import InitECandidate.Runtime.RollbackWorldRecordDecision
import InitECandidate.Runtime.RollbackWorldRead
import InitECandidate.Runtime.LocalScopeRestore
import InitECandidate.Runtime.JournalRecordGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Bound the complete record application in the frozen rollback source. -/
theorem RollbackWorld.record_application_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos items key journal count present value : BitVec 64) (bits : Nat)
    (supported : (widths table) = 20 ∨ (widths table) = 32 ∨ (widths table) = 52)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (setBudget : 3 * capacity.toNat + 2 * (capacity * 2).toNat + (widths table).toNat + 13 + items.toNat * ((capacity * 2).toNat + (widths table).toNat + 4) ≤ state.clock)
    (deleteBudget : capacity.toNat * 57 + 3 ≤ state.clock)
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
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (snapshot : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (registered : table ∈ tables)
    (separated : RollbackPhysicalSeparated widths tables state) :
    ∃ post, evaluateHOLFiniteState state stateRestoreApplyRecord = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post := by
  let record := journal + count * 32
  let recordState := setVarHOLFinite (ofString "r") (.val (.word record)) state
  let tableState := setVarHOLFinite (ofString "t") (.val (.word table)) recordState
  let entry := setVarHOLFinite (ofString "key") (.val (.word key)) tableState
  have entryReady := ready.after_read state entry (widths table) table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have distinctRK : ofString "key" ≠ ofString "r" := by decide
  have distinctRT : ofString "t" ≠ ofString "r" := by decide
  have distinctTK : ofString "key" ≠ ofString "t" := by decide
  have entrySnap : entry.locals.lookup (ofString "snap") = state.locals.lookup (ofString "snap") := by
    have a : ofString "key" ≠ ofString "snap" := by decide
    have b : ofString "t" ≠ ofString "snap" := by decide
    have c : ofString "r" ≠ ofString "snap" := by decide
    simp [entry,tableState,recordState,setVarHOLFinite,FUPDATE,a,b,c]
  have entryWorld := world.after_read (after := entry) rfl rfl rfl rfl rfl entrySnap
  have entrySeparated := separated.after_read (after := entry) rfl rfl rfl rfl rfl
  obtain ⟨bodyPost,decision,postWorld,postSeparated⟩ := RollbackWorld.record_decision_preserves entry widths tables
    table pointer keys stride capacity used values order orderPos items key record present value bits supported entryReady strideBound capacityLarge safePlan setBudget deleteBudget domain
    (by simp [entry,tableState,setVarHOLFinite,FUPDATE,distinctTK])
    (by simp [entry,setVarHOLFinite,FUPDATE])
    (by simp [entry,tableState,recordState,setVarHOLFinite,FUPDATE,distinctRK,distinctRT])
    presentDomain presentCell valueDomain valueCell keyAligned keyWords keyBytes
    journal snapshot count entryWorld registered entrySeparated
  let restoreKey := {bodyPost with locals := HolFiniteMapExact.resVarEq bodyPost.locals (ofString "key",recordState.locals.lookup (ofString "key"))}
  let restoreTable := {restoreKey with locals := HolFiniteMapExact.resVarEq restoreKey.locals (ofString "t",recordState.locals.lookup (ofString "t"))}
  let post := {restoreTable with locals := HolFiniteMapExact.resVarEq restoreTable.locals (ofString "r",state.locals.lookup (ofString "r"))}
  have postSnap : post.locals.lookup (ofString "snap") = bodyPost.locals.lookup (ofString "snap") := by
    exact (restore_other_local restoreTable.locals (ofString "r") (ofString "snap") (state.locals.lookup (ofString "r")) (by decide)).trans
      ((restore_other_local restoreKey.locals (ofString "t") (ofString "snap") (recordState.locals.lookup (ofString "t")) (by decide)).trans
        (restore_other_local bodyPost.locals (ofString "key") (ofString "snap") (recordState.locals.lookup (ofString "key")) (by decide)))
  refine ⟨post,?_,postWorld.after_read rfl rfl rfl rfl rfl postSnap,postSeparated.after_read rfl rfl rfl rfl rfl⟩
  rw [stateRestore_apply_record_shape,evaluate_journal_record_scope32 state journal count _ journalGlobal countGlobal]
  rw [evaluate_stateRestore_record_loads recordState record table key (by simp [recordState,setVarHOLFinite,FUPDATE]) tableDomain tableCell keyDomain keyCell]
  rw [decision]

#print axioms RollbackWorld.record_application_preserves
end InitECandidate.Runtime
