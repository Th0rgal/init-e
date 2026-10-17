import InitECandidate.Runtime.RollbackWorldRegisteredSetSavedValuesIn
import InitECandidate.Runtime.RollbackWorldRegisteredDeleteSavedValuesIn
import InitECandidate.Runtime.StateRestoreRecordDecisionPreservesJournal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual undo set/delete decision preserves the saved-value obligations
of every remaining live record, including when set growth is rejected. -/
theorem RollbackWorld.record_decision_saved_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key record present value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ticks : 2 ^ 74 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (presentDomain : state.memaddrs (record + 16)) (presentCell : state.memory (record + 16) = .word present)
    (valueDomain : state.memaddrs (record + 24)) (valueCell : state.memory (record + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (journalBound : journal.toNat + count.toNat * 32 ≤ 33806089496)
    (journalBefore : journal.toNat + count.toNat * 32 ≤ table.toNat)
    (success : (evaluateHOLFiniteState state stateRestoreRecordDecision).1 = none) :
    JournalSavedValuesIn journal count.toNat watched targets (evaluateHOLFiniteState state stateRestoreRecordDecision).2 := by
  classical
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "r") 16)) = some (.val (.word present)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "r") record 16 r]
    simp [memLoadHOLExact]
    exact ⟨presentDomain,presentCell⟩
  by_cases zero : present = 0
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      rw [evalHOLExact,loaded]
      simp [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL,zero]
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k]
    obtain ⟨post,run,_,_,postSaved,_,_⟩ := RollbackWorld.registered_delete_saved_values_in state widths tables journal snapshot count table key world separated member supported
      watched targets saved journalBound journalBefore (by omega) _ _ args keyAligned keyWords keyBytes
    have selected : evaluateHOLFiniteState state stateRestoreRecordDecision = (none,post) := by
      unfold stateRestoreRecordDecision
      rw [evaluateHOLFiniteState_ite,condition]
      simpa using run
    rw [selected]
    exact postSaved
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
      rw [evalHOLExact,loaded]
      simp [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    have loadedValue : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (hashLocalAddress (ofString "r") 24)) = some (.val (.word value)) := by
      simp only [evalHOLExact,isWfShapeExactHOL]
      rw [eval_hashLocalAddress state (ofString "r") record 24 r]
      simp [memLoadHOLExact]
      exact ⟨valueDomain,valueCell⟩
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)] = some [.val (.word table),.val (.word key),.val (.word value)] := by
      simp only [evalListHOLFinite,evalListHOLExact]
      rw [loadedValue]
      simp [evalHOLExact,t,k]
    have selected : evaluateHOLFiniteState state stateRestoreRecordDecision =
        evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
          [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)]) := by
      unfold stateRestoreRecordDecision
      rw [evaluateHOLFiniteState_ite,condition]
      rfl
    have callSuccess : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
        [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)])).1 = none := by
      rw [← selected]
      exact success
    have preserved := RollbackWorld.registered_set_saved_values_in state widths tables journal snapshot count table key value world member supported
      ticks heapDomain _ _ _ args keyAligned keyWords keyBytes watched targets saved journalBefore journalBound callSuccess
    rw [selected]
    exact preserved

#print axioms RollbackWorld.record_decision_saved_values_in
end InitECandidate.Runtime
