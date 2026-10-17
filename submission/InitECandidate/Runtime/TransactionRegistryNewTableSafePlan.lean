import InitECandidate.Runtime.TransactionRegistryNewTable
import InitECandidate.Runtime.TransactionRegistryHeapBound
import InitECandidate.Runtime.RollbackNewTableDeclarationSafePlan
import InitECandidate.Runtime.HashNewHeapDomainsSafePlan
import InitECandidate.Runtime.HashNewBeforeHeaderSafePlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actually safe constructor plan extends the full transaction registry,
retaining globals, live undo records, and all eight transaction fields. -/
theorem TransactionRegistryWorld.new_table_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer capacity : BitVec 64) (bits : Nat)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (keyArgument capacityArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [keyArgument,capacityArgument] = some [.val (.word (widths pointer)),.val (.word capacity)])
    (power : capacity.toNat = 2 ^ bits) (large : 1 < capacity.toNat)
    (supported : widths pointer = 20 ∨ widths pointer = 32 ∨ widths pointer = 52)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0)
    (headerBefore : ts.toNat + 72 ≤ pointer.toNat)
    (safe : AllocationPlanSafe pointer (htabNewAllocationSizes (widths pointer) capacity))
    (ticks : capacity.toNat + 8 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,post) ∧
      TransactionRegistryWorld widths (insert pointer tables) fieldPointer ts journal snapshot count post ∧
      state.clock ≤ post.clock + capacity.toNat + 8 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos pointer (widths pointer) capacity) (capacity * 8)))) ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) post) continuation;
          (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
  have pointerBound := valid.heap_bounded pointer heap
  have keyBound : (widths pointer).toNat ≤ 52 := by
    rcases supported with same | same | same <;> rw [same] <;> decide
  obtain ⟨tableDomain,headerDomain,wordDomain,byteDomain⟩ := htabNew_heap_domains_of_safe_plan state pointer (widths pointer) capacity pointerBound safe valid.journalWorld.heapDomain
  obtain ⟨post,run,family,apart,cost,remaining,locals,code,domain,endian,globals,heapNext,declaration,_⟩ :=
    rollback_htabNew_registry_declaration_of_safe_plan state widths tables keyArgument capacityArgument pointer capacity bits arguments power tableDomain
      valid.journalWorld.code ticks heap keyBound aligned pointerBound safe headerDomain wordDomain byteDomain large
      (fun table member => (valid.journalWorld.world.ready table member).after_read rfl rfl rfl rfl rfl) valid.journalWorld.separated
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,memory,_⟩ := evaluate_htabNew_call_and_declaration_before_header_of_safe_plan state
    keyArgument capacityArgument pointer (widths pointer) capacity arguments valid.journalWorld.code ticks heap pointerBound aligned safe headerDomain wordDomain byteDomain
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  have beforeMemory : ∀ address : BitVec 64, address.toNat < pointer.toNat → post.memory address = state.memory address := by
    rw [same]; exact memory
  have liveBound : journal.toNat + count.toNat * 32 ≤ 33806089496 := by
    have cap := valid.journalWorld.world.capacity
    have bound := valid.journalWorld.journalBound
    omega
  have recordFrame : ∀ index : Nat, index < count.toNat → ∀ offset ∈ ([0,8,16,24] : List Nat),
      post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) := by
    intro index inside offset member
    have small : offset < 32 := by simp at member; omega
    have interval := journal_undo_field_interval journal count.toNat index offset liveBound inside small
    have cap := valid.journalWorld.world.capacity
    have before := valid.journalBeforeTs
    exact beforeMemory _ (by omega)
  have headers : ∀ table ∈ insert pointer tables, ts.toNat + 72 ≤ table.toNat := by
    intro table member
    rcases Set.mem_insert_iff.mp member with same | old
    · simpa only [same] using headerBefore
    · exact valid.tableHeaders table old
  let logical := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post
  have world : RollbackWorld widths (insert pointer tables) journal snapshot count logical := by
    refine ⟨(globals (ofString "journal_n") (by decide)).trans valid.journalWorld.world.counter,?_,
      (globals (ofString "journal") (by decide)).trans valid.journalWorld.world.journalGlobal,valid.journalWorld.world.capacity,
      valid.journalWorld.world.records.after_frame (after := logical) (Nat.le_refl _) domain recordFrame,?_,?_,?_⟩
    · simp [logical,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro index inside table cell
      have preserved : post.memory (journal + BitVec.ofNat 64 index * 32) = state.memory (journal + BitVec.ofNat 64 index * 32) := by
        simpa using recordFrame index inside 0 (by simp)
      have oldCell := preserved.symm.trans cell
      exact Set.mem_insert_of_mem pointer (valid.journalWorld.world.references index inside table oldCell)
    · intro table member
      exact (family table member).after_read rfl rfl rfl rfl rfl
    · intro table member
      have header := headers table member
      have cap := valid.journalWorld.world.capacity
      have before := valid.journalBeforeTs
      omega
  have journalWorld : JournalRuntimeWorld widths (insert pointer tables) journal snapshot count post := by
    refine ⟨world,apart,valid.journalWorld.journalBound,valid.journalWorld.journalAligned,?_,?_,
      (globals (ofString "journal_cap") (by decide)).trans valid.journalWorld.capacity,code.trans valid.journalWorld.code,?_⟩
    · intro table member
      have header := headers table member
      have before := valid.journalBeforeTs
      omega
    · intro address upper
      rw [domain]; exact valid.journalWorld.heapDomain address upper
    · intro table member
      rcases Set.mem_insert_iff.mp member with same | old
      · simpa only [same] using supported
      · exact valid.journalWorld.supported table old
  refine ⟨post,run,⟨journalWorld,valid.fields.after_frontier_frame state post ts fieldPointer pointer (by omega) headerBefore beforeMemory,
    (globals (ofString "ts") (by decide)).trans valid.tsGlobal,valid.tsBound,valid.journalBeforeTs,?_,headers⟩,
    cost,remaining,locals,heapNext,declaration⟩
  intro table member
  exact Set.mem_insert_of_mem pointer (valid.fieldRegistry member)

#print axioms TransactionRegistryWorld.new_table_of_safe_plan
end InitECandidate.Runtime
