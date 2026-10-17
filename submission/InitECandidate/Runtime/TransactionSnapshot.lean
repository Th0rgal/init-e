import InitECandidate.Runtime.TransactionRestoreCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The snapshot is a logical observation, not stored transaction data.
Choosing another snapshot does not change the executing state or journal. -/
theorem TransactionRuntimeWorld.with_snapshot {F : Type}
    {widths : BitVec 64 → BitVec 64} {fieldPointer ts journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count state)
    (nextSnapshot : BitVec 64) :
    TransactionRuntimeWorld widths fieldPointer ts journal nextSnapshot count state := by
  let bound := setVarHOLFinite (ofString "snap") (.val (.word nextSnapshot)) state
  have world : RollbackWorld widths (stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅) journal nextSnapshot count bound := by
    refine ⟨valid.journalWorld.world.counter,?_,valid.journalWorld.world.journalGlobal,valid.journalWorld.world.capacity,
      valid.journalWorld.world.records.after_frame (after := bound) (Nat.le_refl _) rfl (by intro index inside offset member; rfl),
      valid.journalWorld.world.references,?_,valid.journalWorld.world.layout⟩
    · simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro table member
      exact (valid.journalWorld.world.ready table member).after_read rfl rfl rfl rfl rfl
  exact ⟨⟨world,valid.journalWorld.separated,valid.journalWorld.journalBound,valid.journalWorld.journalAligned,
    valid.journalWorld.journalHeaders,valid.journalWorld.heapDomain,valid.journalWorld.capacity,valid.journalWorld.code,
    valid.journalWorld.supported⟩,valid.fields,valid.tsGlobal,valid.tsBound,valid.journalBeforeTs,valid.tableHeaders⟩

/-- Restore to any evaluated saved count using the original call; the logical
snapshot parameter need not have been fixed when the transaction was initialized. -/
theorem TransactionRuntimeWorld.restore_call_at {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (fieldPointer ts journal snapshot count nextSnapshot : BitVec 64)
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count state)
    (argument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word nextSnapshot)])
    (budget : 2 ^ 92 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_restore") [argument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 92 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → ∃ n : BitVec 64, TransactionRuntimeWorld widths fieldPointer ts journal nextSnapshot n output.2 ∧ n.toNat ≤ nextSnapshot.toNat) :=
  (valid.with_snapshot nextSnapshot).restore_call state widths fieldPointer ts journal nextSnapshot count argument arguments budget

#print axioms TransactionRuntimeWorld.with_snapshot
#print axioms TransactionRuntimeWorld.restore_call_at
end InitECandidate.Runtime
