import InitECandidate.Runtime.RegistryRestoreLoop
import InitECandidate.Runtime.RollbackWorldLoopRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full transaction rollback retains the transaction world, registered table
values, and remaining saved journal values on normal completion. -/
theorem TransactionRegistryWorld.restore_loop_registered_values_in {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)} {fieldPointer ts journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (snapshotLocal : state.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (budget : 2 ^ 94 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.while stateRestoreCondition stateRestoreLoopBody) = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 94 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ n : BitVec 64, TransactionRegistryWorld widths tables fieldPointer ts journal snapshot n post ∧
        post.locals.lookup (ofString "snap") = some (.val (.word snapshot)) ∧ n.toNat ≤ snapshot.toNat ∧
        (∀ other ∈ watched, HashTableValuesIn other targets post) ∧ JournalSavedValuesIn journal n.toNat watched targets post) ∧
      (∀ value, result ≠ some (.returned value)) := by
  have actualWorld : RollbackWorld widths tables journal snapshot count state :=
    valid.journalWorld.world.after_read rfl rfl rfl rfl rfl (by
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using snapshotLocal)
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ :=
    valid.restore_loop snapshotLocal (by omega)
  obtain ⟨checkedResult,checked,checkedRun,_,_,_,checkedCompleted,_⟩ :=
    actualWorld.loop_bounded_registered_values_in valid.journalWorld.separated valid.journalWorld.heapDomain
      watched targets watchedSubset registered saved budget
  have equal := run.symm.trans checkedRun
  have sameResult : result = checkedResult := congrArg Prod.fst equal
  have samePost : post = checked := congrArg Prod.snd equal
  subst checkedResult
  subst checked
  refine ⟨result,post,run,(by omega),remaining,noTimeout,?_,noReturn⟩
  intro normal
  obtain ⟨n,postWorld,postSnapshot,finished⟩ := completed normal
  obtain ⟨m,checkedWorld,_,_,_,postRegistered,postSaved⟩ := checkedCompleted normal
  have sameCount : m = n := by
    have equal := checkedWorld.counter.symm.trans postWorld.journalWorld.world.counter
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
  subst m
  exact ⟨n,postWorld,postSnapshot,finished,postRegistered,postSaved⟩

#print axioms TransactionRegistryWorld.restore_loop_registered_values_in
end InitECandidate.Runtime
