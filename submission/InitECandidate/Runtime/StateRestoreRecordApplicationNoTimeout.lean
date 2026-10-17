import InitECandidate.Runtime.StateRestoreRecordLoadScopes
import InitECandidate.Runtime.StateRestoreRecordDecisionNoTimeout
import InitECandidate.Runtime.JournalRecordGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Bound the complete record application in the frozen rollback source. -/
theorem HashTableReady.restore_record_application_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count present value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
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
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (evaluateHOLFiniteState state stateRestoreApplyRecord).1 ≠ some .timeOut ∧
    state.clock ≤ (evaluateHOLFiniteState state stateRestoreApplyRecord).2.clock + 2 ^ 72 ∧
      (evaluateHOLFiniteState state stateRestoreApplyRecord).2.clock ≤ state.clock := by
  let record := journal + count * 32
  let recordState := setVarHOLFinite (ofString "r") (.val (.word record)) state
  let tableState := setVarHOLFinite (ofString "t") (.val (.word table)) recordState
  let entry := setVarHOLFinite (ofString "key") (.val (.word key)) tableState
  have entryReady := ready.after_read state entry keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have distinctRK : ofString "key" ≠ ofString "r" := by decide
  have distinctRT : ofString "t" ≠ ofString "r" := by decide
  have distinctTK : ofString "key" ≠ ofString "t" := by decide
  have decision := entryReady.restore_record_decision_no_timeout entry keyLength table pointer keys stride capacity used values order orderPos items key record present value bits supported strideBound capacityLarge ticks domain
    (by simp [entry,tableState,setVarHOLFinite,FUPDATE,distinctTK])
    (by simp [entry,setVarHOLFinite,FUPDATE])
    (by simp [entry,tableState,recordState,setVarHOLFinite,FUPDATE,distinctRK,distinctRT])
    presentDomain presentCell valueDomain valueCell keyAligned keyWords keyBytes
  rw [stateRestore_apply_record_shape,evaluate_journal_record_scope32 state journal count _ journalGlobal countGlobal]
  rw [evaluate_stateRestore_record_loads recordState record table key (by simp [recordState,setVarHOLFinite,FUPDATE]) tableDomain tableCell keyDomain keyCell]
  exact decision

#print axioms HashTableReady.restore_record_application_no_timeout
end InitECandidate.Runtime
