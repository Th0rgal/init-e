import InitECandidate.Runtime.RegistryRestoreBodyRegisteredValuesIn
import InitECandidate.Runtime.RollbackWorldCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original restore call binds the snapshot argument, consumes at
most2^94+1 clocks and retains the complete transaction invariant on success. -/
theorem TransactionRegistryWorld.restore_call_registered_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (fieldPointer ts journal snapshot count : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (argument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word snapshot)])
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (budget : 2 ^ 94 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_restore") [argument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 94 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → ∃ n : BitVec 64, TransactionRegistryWorld widths tables fieldPointer ts journal snapshot n output.2 ∧ n.toNat ≤ snapshot.toNat ∧
        (∀ other ∈ watched, HashTableValuesIn other targets output.2) ∧ JournalSavedValuesIn journal n.toNat watched targets output.2) := by
  have bounded := rollback_world_call_bounded_no_timeout state widths tables
    journal snapshot count valid.journalWorld.world valid.journalWorld.separated valid.journalWorld.heapDomain argument arguments valid.journalWorld.code (by omega)
  refine ⟨bounded.1,(by have := bounded.2.1; omega),bounded.2.2,?_⟩
  intro success
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "snap",.val (.word snapshot))
  let entry := callEntryStateHOLFinite state callee
  have entryValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count entry := valid.after_read rfl rfl rfl rfl rfl
  have snap : entry.locals.lookup (ofString "snap") = some (.val (.word snapshot)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,body,_,_,_,completed⟩ := entryValid.restore_body_registered_values_in snap watched targets watchedSubset (fun other belongs => (registered other belongs).after_read rfl rfl rfl)
    (saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)) (by change 2 ^ 94 ≤ state.clock - 1; omega)
  have preserves : ∀ value, (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_state_restore)).1 = some (.returned value) →
      ∃ n : BitVec 64, TransactionRegistryWorld widths tables fieldPointer ts journal snapshot n
        (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_state_restore)).2 ∧ n.toNat ≤ snapshot.toNat ∧
        (∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_state_restore)).2) ∧
        JournalSavedValuesIn journal n.toNat watched targets (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_state_restore)).2 := by
    rw [body]
    exact completed
  have installed : state.code.lookup (ofString "state_restore") =
      some ([(ofString "snap",.one)],sourceFunctionBody Guest.guestFn_state_restore,.one) := by
    rw [valid.journalWorld.code]; exact originalRuntimeCode_stateRestore_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "state_restore") (ofString "snap")
    (sourceFunctionBody Guest.guestFn_state_restore) snapshot installed
  simp only [evaluateHOLFiniteState_call,arguments] at success ⊢
  rw [lookup] at success ⊢
  dsimp only at success ⊢
  have clock : state.clock ≠ 0 := by omega
  simp only [if_neg clock] at success ⊢
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_state_restore) with
  | mk result afterBody =>
      rw [bodyRun] at success preserves
      cases result with
      | none => cases success
      | some result =>
          cases result with
          | returned value =>
              dsimp only at success ⊢
              split at success
              · rename_i goodShape
                simp only [goodShape,if_true]
                obtain ⟨n,world,done,postRegistered,postSaved⟩ := preserves value rfl
                exact ⟨n,world.after_read rfl rfl rfl rfl rfl,done,(fun other belongs => (postRegistered other belongs).after_read rfl rfl rfl),
                  postSaved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)⟩
              · cases success
          | _ => cases success

#print axioms TransactionRegistryWorld.restore_call_registered_values_in
end InitECandidate.Runtime
