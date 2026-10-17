import InitECandidate.Runtime.TransactionRegistryWorldFrame
import InitECandidate.Runtime.RollbackRegistryLaterRecord
import InitECandidate.Runtime.RollbackWorldFrame
import InitECandidate.Runtime.JournalRecordAppendFrame
import InitECandidate.Runtime.StateFreshTxFieldsRecordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Writing four words in an allocation beyond the live tables preserves the
complete transaction registry, undo records and original transaction fields. -/
theorem TransactionRegistryWorld.after_four_words {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (destination a b c d : BitVec 64)
    (bounded : destination.toNat + 32 ≤ 33806089496)
    (afterHeader : ts.toNat + 72 ≤ destination.toNat)
    (outside : ∀ table ∈ tables, ∀ pointer keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits pointer state →
      reverse.toNat + capacity.toNat * 8 ≤ destination.toNat) :
    TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count
      (journalRecordPost32 state destination a b c d) := by
  let post := journalRecordPost32 state destination a b c d
  obtain ⟨family,apart⟩ := rollback_registry_after_later_record state widths tables destination a b c d
    (fun table member => (valid.journalWorld.world.ready table member).after_read rfl rfl rfl rfl rfl)
    valid.journalWorld.separated bounded outside
  have liveBound : journal.toNat + count.toNat * 32 ≤ 33806089496 := by
    have cap := valid.journalWorld.world.capacity
    have bound := valid.journalWorld.journalBound
    omega
  have liveBefore : journal.toNat + count.toNat * 32 ≤ destination.toNat := by
    have cap := valid.journalWorld.world.capacity
    have before := valid.journalBeforeTs
    omega
  have recordFrame := journalRecordPost32_prefix_frame state journal destination a b c d count.toNat liveBound bounded liveBefore
  have world : RollbackWorld widths tables journal snapshot count
      (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) := by
    apply valid.journalWorld.world.after_frame (Nat.le_refl _)
    · exact valid.journalWorld.world.counter
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · exact valid.journalWorld.world.journalGlobal
    · rfl
    · exact recordFrame
    · intro table member
      exact (family table member).after_read rfl rfl rfl rfl rfl
  have start : (ts + (8 : BitVec 64)).toNat = ts.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change ts.toNat + 8 < 2 ^ 64; have := valid.tsBound; omega)]
    rfl
  have fieldFrame := journalRecordPost32_prefix_frame state (ts + 8) destination a b c d 2 (by omega) bounded (by omega)
  exact ⟨⟨world,apart,valid.journalWorld.journalBound,valid.journalWorld.journalAligned,valid.journalWorld.journalHeaders,
    valid.journalWorld.heapDomain,valid.journalWorld.capacity,valid.journalWorld.code,valid.journalWorld.supported⟩,
    valid.fields.after_two_record_frame fieldFrame,valid.tsGlobal,valid.tsBound,valid.journalBeforeTs,valid.fieldRegistry,valid.tableHeaders⟩

#print axioms TransactionRegistryWorld.after_four_words
end InitECandidate.Runtime
