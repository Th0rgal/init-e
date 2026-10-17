import InitECandidate.Runtime.RollbackWorldRecordApplicationValuesInFamily
import InitECandidate.Runtime.RollbackWorldRecordApplicationSavedValuesIn
import InitECandidate.Runtime.RollbackWorldIterationAllPlans
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally returning undo iteration preserves watched values and the saved
values of all records still in the journal. -/
theorem RollbackWorld.iteration_registered_values_in {F : Type} {widths : BitVec 64 → BitVec 64}
    {tables : Set (BitVec 64)} {journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F} (valid : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (active : 0 < stateRestoreRank state) (ticks : 2 ^ 74 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registeredValues : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (success : (evaluateHOLFiniteState state stateRestoreLoopBody).1 = none) :
    (∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState state stateRestoreLoopBody).2) ∧
    JournalSavedValuesIn journal (count - 1).toNat watched targets (evaluateHOLFiniteState state stateRestoreLoopBody).2 := by
  obtain ⟨table,key,present,value,tableReady,supported,t,k,p,v,aligned,words,bytes⟩ := valid.select_last active
  obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,strideBound,large⟩ := tableReady
  have rank := stateRestoreRank_of_bindings state count snapshot valid.counter valid.snapshotLocal
  have numeric := (stateRestore_rank_decreases count snapshot (by omega)).1
  have inside : (count - 1).toNat < count.toNat := by omega
  obtain ⟨_,_,_,_,_,_,_,_,_,_,fields,_⟩ := valid.records.1 (count - 1).toNat inside
  have indexWord : BitVec.ofNat 64 (count - 1).toNat = count - 1 := by
    apply BitVec.eq_of_toNat_eq
    change (count - 1).toNat % 2 ^ 64 = (count - 1).toNat
    exact Nat.mod_eq_of_lt (count - 1).isLt
  have domains : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (journal + (count - 1) * 32 + BitVec.ofNat 64 offset) := by
    simpa only [indexWord] using fields
  have registered : table ∈ tables := by
    apply valid.references (count - 1).toNat inside table
    simpa only [indexWord] using t
  let entry := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count - 1))) state
  have entryWorld := valid.decrement (by omega)
  have entrySeparated := separated.after_global (ofString "journal_n") (.val (.word (count - 1))) (by decide)
  have run : evaluateHOLFiniteState state stateRestoreLoopBody = evaluateHOLFiniteState entry stateRestoreApplyRecord := by
    rw [stateRestore_loop_body_shape]
    exact evaluate_seq_none (evaluate_stateRestore_decrement state count valid.counter) rfl
  have applicationSuccess : (evaluateHOLFiniteState entry stateRestoreApplyRecord).1 = none := by
    rw [← run]
    exact success
  have entrySaved : JournalSavedValuesIn journal ((count - 1).toNat + 1) watched targets entry := by
    have equal : (count - 1).toNat + 1 = count.toNat := by omega
    rw [equal]
    exact saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)
  have family := entryWorld.record_application_values_in_family entry widths tables journal snapshot (count - 1) table key present value entrySeparated registered supported ticks heapDomain
    entryWorld.journalGlobal entryWorld.counter
    (show state.memaddrs (journal + (count - 1) * 32) from by simpa using domains 0 (by simp)) t (domains 8 (by simp)) k
    (domains 16 (by simp)) p (domains 24 (by simp)) v aligned words bytes
    watched targets watchedSubset (fun other belongs => (registeredValues other belongs).after_read rfl rfl rfl) entrySaved applicationSuccess
  have journalBefore := entryWorld.layout table registered
  have journalBound : journal.toNat + (count - 1).toNat * 32 ≤ 33806089496 := by
    have := ready.live.arrays.headerKeys
    have := ready.live.arrays.keysBefore
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have remainingSaved := entryWorld.record_application_saved_values_in entry widths tables journal snapshot (count - 1) table key present value entrySeparated registered supported ticks heapDomain
    entryWorld.journalGlobal entryWorld.counter
    (show state.memaddrs (journal + (count - 1) * 32) from by simpa using domains 0 (by simp)) t (domains 8 (by simp)) k
    (domains 16 (by simp)) p (domains 24 (by simp)) v aligned words bytes
    watched targets entrySaved journalBound journalBefore applicationSuccess
  rw [run]
  exact ⟨family,remainingSaved⟩

#print axioms RollbackWorld.iteration_registered_values_in
end InitECandidate.Runtime
