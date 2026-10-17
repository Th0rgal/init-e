import InitECandidate.Runtime.TransactionRegistryWorld
import InitECandidate.Runtime.RollbackWorldIterationBoundedFields
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One actual active rollback iteration retains the complete transaction
invariant and snapshot binding, or exits exceptionally without a false success. -/
theorem TransactionRegistryWorld.restore_iteration {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)} {fieldPointer ts journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (snapshotLocal : state.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (active : 0 < stateRestoreRank state) (ticks : 2 ^ 72 + 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateRestoreLoopBody = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 72 + 1) ∧ post.clock ≤ state.clock ∧
      ((result = none ∧ TransactionRegistryWorld widths tables fieldPointer ts journal snapshot (count - 1) post ∧
        post.locals.lookup (ofString "snap") = some (.val (.word snapshot)) ∧ stateRestoreRank post < stateRestoreRank state) ∨
       (result ≠ none ∧ result ≠ some .timeOut ∧ result ≠ some .continue ∧ result ≠ some .break ∧
        (∀ value, result ≠ some (.returned value)))) := by
  have actualWorld : RollbackWorld widths tables journal snapshot count state :=
    valid.journalWorld.world.after_read rfl rfl rfl rfl rfl (by
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using snapshotLocal)
  obtain ⟨result,post,run,cost,remaining,outcome⟩ := actualWorld.iteration_bounded_fields valid.journalWorld.separated active ticks
    valid.journalWorld.heapDomain ts fieldPointer valid.fields valid.tableHeaders
  refine ⟨result,post,run,cost,remaining,?_⟩
  rcases outcome with success | failure
  · obtain ⟨normal,world,apart,decrease,fields,globals⟩ := success
    have metadata := evaluateHOLFiniteState_metadata state stateRestoreLoopBody
    rw [run] at metadata
    have nextJournal : JournalRuntimeWorld widths tables journal snapshot (count - 1) post := by
      refine ⟨world.after_logical_frame rfl rfl rfl rfl rfl,apart,valid.journalWorld.journalBound,
        valid.journalWorld.journalAligned,valid.journalWorld.journalHeaders,?_,?_,metadata.1.trans valid.journalWorld.code,valid.journalWorld.supported⟩
      · intro address upper
        rw [metadata.2.1]
        exact valid.journalWorld.heapDomain address upper
      · exact (globals (ofString "journal_cap") (by decide) (by decide)).trans valid.journalWorld.capacity
    exact Or.inl ⟨normal,⟨nextJournal,fields,(globals (ofString "ts") (by decide) (by decide)).trans valid.tsGlobal,
      valid.tsBound,valid.journalBeforeTs,valid.fieldRegistry,valid.tableHeaders⟩,world.snapshotLocal,decrease⟩
  · exact Or.inr failure

#print axioms TransactionRegistryWorld.restore_iteration
end InitECandidate.Runtime
