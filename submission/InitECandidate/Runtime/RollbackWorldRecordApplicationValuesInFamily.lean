import InitECandidate.Runtime.RollbackWorldRecordDecisionValuesInFamily
import InitECandidate.Runtime.StateRestoreRecordLoadScopes
import InitECandidate.Runtime.RollbackWorldRead
import InitECandidate.Runtime.JournalRecordGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual undo-record application derives the restored pointer's membership
from the saved journal invariant and retains table membership through all record
loads and caller-local restoration. -/
theorem RollbackWorld.record_application_values_in_family {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key present value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ticks : 2 ^ 74 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
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
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal (count.toNat + 1) watched targets state)
    (success : (evaluateHOLFiniteState state stateRestoreApplyRecord).1 = none) :
    ∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState state stateRestoreApplyRecord).2 := by
  let record := journal + count * 32
  let recordState := setVarHOLFinite (ofString "r") (.val (.word record)) state
  let tableState := setVarHOLFinite (ofString "t") (.val (.word table)) recordState
  let entry := setVarHOLFinite (ofString "key") (.val (.word key)) tableState
  have distinctRK : ofString "key" ≠ ofString "r" := by decide
  have distinctRT : ofString "t" ≠ ofString "r" := by decide
  have distinctTK : ofString "key" ≠ ofString "t" := by decide
  have entrySnap : entry.locals.lookup (ofString "snap") = state.locals.lookup (ofString "snap") := by
    have a : ofString "key" ≠ ofString "snap" := by decide
    have b : ofString "t" ≠ ofString "snap" := by decide
    have c : ofString "r" ≠ ofString "snap" := by decide
    simp [entry,tableState,recordState,setVarHOLFinite,FUPDATE,a,b,c]
  have entryWorld := world.after_read (after := entry) rfl rfl rfl rfl rfl entrySnap
  have fullRun : evaluateHOLFiniteState state stateRestoreApplyRecord =
      (let output := evaluateHOLFiniteState entry stateRestoreRecordDecision;
        let restoredKey := {output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "key",recordState.locals.lookup (ofString "key"))};
        let restoredTable := {restoredKey with locals := HolFiniteMapExact.resVarEq restoredKey.locals (ofString "t",recordState.locals.lookup (ofString "t"))};
        (output.1,{restoredTable with locals := HolFiniteMapExact.resVarEq restoredTable.locals (ofString "r",state.locals.lookup (ofString "r"))})) := by
    rw [stateRestore_apply_record_shape,evaluate_journal_record_scope32 state journal count _ journalGlobal countGlobal]
    rw [evaluate_stateRestore_record_loads recordState record table key (by simp [recordState,setVarHOLFinite,FUPDATE]) tableDomain tableCell keyDomain keyCell]
  have decisionSuccess : (evaluateHOLFiniteState entry stateRestoreRecordDecision).1 = none := by
    simpa only [fullRun] using success
  have valueMember : present ≠ 0 → table ∈ watched → value ∈ targets := by
    intro occupied watchedMember
    exact saved count.toNat (by omega) table present value (by simpa using tableCell)
      (by simpa using presentCell) (by simpa using valueCell) watchedMember occupied
  have entrySeparated := separated.after_read (after := entry) rfl rfl rfl rfl rfl
  have preserved := entryWorld.record_decision_values_in_family entry widths tables journal snapshot count table key record present value entrySeparated member supported ticks heapDomain
    (by simp [entry,tableState,setVarHOLFinite,FUPDATE,distinctTK])
    (by simp [entry,setVarHOLFinite,FUPDATE])
    (by simp [entry,tableState,recordState,setVarHOLFinite,FUPDATE,distinctRK,distinctRT])
    presentDomain presentCell valueDomain valueCell keyAligned keyWords keyBytes watched targets watchedSubset (fun other belongs => (registered other belongs).after_read rfl rfl rfl) valueMember decisionSuccess
  rw [fullRun]
  intro other belongs
  exact (preserved other belongs).after_read rfl rfl rfl

#print axioms RollbackWorld.record_application_values_in_family
end InitECandidate.Runtime
