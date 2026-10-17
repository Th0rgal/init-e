import InitECandidate.Runtime.TransactionRegistryWorldFrame
import InitECandidate.Runtime.RollbackWorldHeapAdvance
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful allocator call advances every registered table's common
frontier while retaining the journal, transaction fields and arbitrary locals. -/
theorem TransactionRegistryWorld.allocate {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer size : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (argument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word size)])
    (clock : state.clock ≠ 0)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer size).toNat ≤ 33806089496) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "alloc") [argument]) = (none,post) ∧
      TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count post ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧ post.locals = state.locals ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "alloc") [argument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) post) continuation;
          (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
  obtain ⟨post,run,ticks,memory,locals,code,domain,_,endian,globals,declaration⟩ :=
    evaluate_alloc_call_and_declaration state argument pointer size arguments valid.journalWorld.code clock heap request finish
  have heapNext : post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have frame : HeapGlobalsFrame state post := by
    intro name different
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have covers := allocationEnd_covers pointer size (allocationGuard_sum_bound pointer size pointerBound request)
  let logical := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post
  have apart := valid.journalWorld.separated.after_read (after := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state) rfl rfl rfl rfl rfl
  obtain ⟨world,postApart⟩ := valid.journalWorld.world.advance_heap (after := logical) apart pointer (allocationEnd pointer size)
    heap heapNext (by omega) finish covers.2.2 memory frame
    (by simp only [logical,setVarHOLFinite,locals]) code domain endian
  have nextJournal : JournalRuntimeWorld widths tables journal snapshot count post := by
    refine ⟨world,postApart.after_read rfl rfl rfl rfl rfl,valid.journalWorld.journalBound,
      valid.journalWorld.journalAligned,valid.journalWorld.journalHeaders,?_,
      (frame (ofString "journal_cap") (by decide)).trans valid.journalWorld.capacity,code.trans valid.journalWorld.code,valid.journalWorld.supported⟩
    intro address upper
    rw [domain]; exact valid.journalWorld.heapDomain address upper
  exact ⟨post,run,⟨nextJournal,valid.fields.after_memory memory,(frame (ofString "ts") (by decide)).trans valid.tsGlobal,
    valid.tsBound,valid.journalBeforeTs,valid.fieldRegistry,valid.tableHeaders⟩,ticks,memory,locals,heapNext,declaration⟩

#print axioms TransactionRegistryWorld.allocate
end InitECandidate.Runtime
