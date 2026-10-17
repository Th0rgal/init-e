import InitECandidate.Runtime.TransactionRegistryWorldFrame
import InitECandidate.Runtime.RollbackWorldRegisteredSetFields
import InitECandidate.Runtime.RollbackWorldRegisteredSetValuesInFamily
import InitECandidate.Runtime.RollbackWorldRegisteredSetSavedValuesIn
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A plain table set retains the transaction world and both pointer invariants
on normal return, without appending an undo record. All allocation plans are covered. -/
theorem TransactionRegistryWorld.table_set_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count table key value : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (snapshotLocal : state.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (member : table ∈ tables)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (newRegistered : table ∈ watched → value ∈ targets)
    (ticks : 2 ^ 74 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + 2 ^ 74 ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count output.2 ∧
        (∀ other ∈ watched, HashTableValuesIn other targets output.2) ∧ JournalSavedValuesIn journal count.toNat watched targets output.2) := by
  have world : RollbackWorld widths tables journal snapshot count state :=
    valid.journalWorld.world.after_read rfl rfl rfl rfl rfl (by
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using snapshotLocal)
  have supported := valid.journalWorld.supported table member
  have cost := world.registered_set_bounded state widths tables journal snapshot count table key value valid.journalWorld.separated member supported
    (by omega) valid.journalWorld.heapDomain tableArgument keyArgument valueArgument arguments aligned words bytes
  have outcome := world.registered_set_all_plans state widths tables journal snapshot count table key value valid.journalWorld.separated member supported
    (by omega) valid.journalWorld.heapDomain tableArgument keyArgument valueArgument arguments aligned words bytes
  rcases outcome with good | failure
  · obtain ⟨post,run,postWorld,postSeparated⟩ := good
    have normal : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 = none := by rw [run]
    have fields := world.registered_set_success_fields state widths tables journal snapshot count table key value valid.journalWorld.separated member supported
      ts fieldPointer valid.fields (valid.tableHeaders table member) (by omega) valid.journalWorld.heapDomain
      tableArgument keyArgument valueArgument arguments aligned words bytes normal
    have globals := world.registered_set_success_heap_frame state widths tables journal snapshot count table key value valid.journalWorld.separated member supported
      (by omega) valid.journalWorld.heapDomain tableArgument keyArgument valueArgument arguments aligned words bytes normal
    have valuesIn := world.registered_set_values_in_family state widths tables journal snapshot count table key value valid.journalWorld.separated member supported
      ticks valid.journalWorld.heapDomain tableArgument keyArgument valueArgument arguments aligned words bytes watched targets watchedSubset registered newRegistered normal
    have savedIn := world.registered_set_saved_values_in state widths tables journal snapshot count table key value member supported
      ticks valid.journalWorld.heapDomain tableArgument keyArgument valueArgument arguments aligned words bytes watched targets saved
      (world.layout table member) (by have := world.capacity; have := valid.journalWorld.journalBound; omega) normal
    have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])
    rw [run] at cost fields globals valuesIn savedIn metadata ⊢
    refine ⟨by simp,(by have := cost.1; omega),cost.2,?_⟩
    intro _
    have journalWorld : JournalRuntimeWorld widths tables journal snapshot count post := by
      refine ⟨postWorld.after_logical_frame rfl rfl rfl rfl rfl,postSeparated,valid.journalWorld.journalBound,
        valid.journalWorld.journalAligned,valid.journalWorld.journalHeaders,?_,?_,metadata.1.trans valid.journalWorld.code,valid.journalWorld.supported⟩
      · intro address upper
        rw [metadata.2.1]
        exact valid.journalWorld.heapDomain address upper
      · exact (globals (ofString "journal_cap") (by decide)).trans valid.journalWorld.capacity
    exact ⟨⟨journalWorld,fields,(globals (ofString "ts") (by decide)).trans valid.tsGlobal,
      valid.tsBound,valid.journalBeforeTs,valid.fieldRegistry,valid.tableHeaders⟩,valuesIn,savedIn⟩
  · exact ⟨failure.2.1,(by have := cost.1; omega),cost.2,fun normal => False.elim (failure.1 normal)⟩

#print axioms TransactionRegistryWorld.table_set_registered_values_in
end InitECandidate.Runtime
