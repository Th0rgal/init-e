import InitECandidate.Runtime.HeapReleaseCall
import InitECandidate.Runtime.RollbackWorldHeapRestore
import InitECandidate.Runtime.TransactionRegistryHeapExists
import InitECandidate.Runtime.TransactionRegistryWorldFrame
import InitECandidate.Runtime.HashTableValuesInMutation
import InitECandidate.Runtime.JournalSavedValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual release of temporary scratch allocations retains the complete
transaction and pointer invariants when the saved mark covers all live tables. -/
theorem TransactionRegistryWorld.release_heap_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count mark : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (argument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word mark)])
    (bounded : mark.toNat ≤ 33806089496) (aligned : mark.toNat % 8 = 0)
    (allocated : ∀ table ∈ tables, ∀ op keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits op state →
      reverse.toNat + capacity.toNat * 8 ≤ mark.toNat)
    (watched targets : Set (BitVec 64))
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (ticks : state.clock ≠ 0) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "heap_release") [argument]) = (none,post) ∧
      post.clock = state.clock - 1 ∧ TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count post ∧
      (∀ other ∈ watched, HashTableValuesIn other targets post) ∧ JournalSavedValuesIn journal count.toNat watched targets post ∧
      post.locals = state.locals ∧ post.memory = state.memory ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  obtain ⟨current,heap,_,_,_⟩ := valid.heap_exists
  obtain ⟨post,run,clock,memory,globals,locals,code,domain,endian⟩ := evaluate_heapRelease_call state argument mark current
    valid.journalWorld.code args heap ticks
  have heapMark : post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have frame : HeapGlobalsFrame state post := by
    intro name different
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  let logicalBefore := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state
  let logicalAfter := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post
  have logicalAllocated : ∀ table ∈ tables, ∀ op keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits op logicalBefore →
      reverse.toNat + capacity.toNat * 8 ≤ mark.toNat := by
    intro table member op keys stride capacity used values order reverse items bits ready
    exact allocated table member op keys stride capacity used values order reverse items bits
      (ready.after_read logicalBefore state (widths table) table keys stride capacity used values order reverse items bits op rfl rfl rfl rfl rfl)
  have logicalLocals : logicalAfter.locals = logicalBefore.locals := by
    simp only [logicalAfter,logicalBefore,setVarHOLFinite,locals]
  obtain ⟨world,apart⟩ := valid.journalWorld.world.restore_heap
    (after := logicalAfter) (valid.journalWorld.separated.after_read (after := logicalBefore) rfl rfl rfl rfl rfl)
    mark heapMark bounded aligned logicalAllocated memory frame logicalLocals code domain endian
  have journalWorld : JournalRuntimeWorld widths tables journal snapshot count post := by
    refine ⟨world,apart.after_read rfl rfl rfl rfl rfl,valid.journalWorld.journalBound,
      valid.journalWorld.journalAligned,valid.journalWorld.journalHeaders,?_,?_,code.trans valid.journalWorld.code,valid.journalWorld.supported⟩
    · intro address upper
      rw [domain]
      exact valid.journalWorld.heapDomain address upper
    · exact (frame (ofString "journal_cap") (by decide)).trans valid.journalWorld.capacity
  have postValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count post :=
    ⟨journalWorld,valid.fields.after_memory memory,(frame (ofString "ts") (by decide)).trans valid.tsGlobal,
      valid.tsBound,valid.journalBeforeTs,valid.fieldRegistry,valid.tableHeaders⟩
  exact ⟨post,run,clock,postValid,(fun other belongs => (registered other belongs).after_read memory domain endian),
    saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; exact congrFun memory _),locals,memory,heapMark⟩

#print axioms TransactionRegistryWorld.release_heap_registered_values_in
end InitECandidate.Runtime
