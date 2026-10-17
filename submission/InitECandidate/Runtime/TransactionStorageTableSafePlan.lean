import InitECandidate.Runtime.TransactionStorageTable
import InitECandidate.Runtime.TransactionRegistryNewTableSafePlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The storage constructor assigns its fresh pointer and preserves the full
transaction registry for every actually safe plan, without reserving 762 bytes. -/
theorem TransactionRegistryWorld.new_storage_table_local_of_safe_plan {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer oldValue : BitVec 64) (name : MlS)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (localWord : state.locals.lookup name = some (.val (.word oldValue)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (safe : AllocationPlanSafe pointer (htabNewAllocationSizes 32 8)) (ticks : 16 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "htab_new") [.const 32,.const 8]) = (none,post) ∧
      TransactionRegistryWorld (withTableWidth widths pointer 32) (insert pointer tables) fieldPointer ts journal snapshot count post ∧
      state.clock ≤ post.clock + 16 ∧ post.clock ≤ state.clock ∧ post.locals.lookup name = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos pointer 32 8) (8 * 8)))) := by
  let updated := withTableWidth widths pointer (32 : BitVec 64)
  have fresh := valid.with_fresh_width pointer (32 : BitVec 64) heap
  have width : updated pointer = (32 : BitVec 64) := by simp [updated,withTableWidth]
  have facts := valid.heap_facts pointer heap
  have pointerBound := valid.heap_bounded pointer heap
  have updatedSafe : AllocationPlanSafe pointer (htabNewAllocationSizes (updated pointer) 8) := by
    rw [width]; exact safe
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.const 32,.const 8] = some [.val (.word (updated pointer)),.val (.word (8 : BitVec 64))] := by rw [width]; rfl
  obtain ⟨post,run,postValid,cost,remaining,_,heapNext,_⟩ := fresh.new_table_of_safe_plan state updated tables fieldPointer ts journal snapshot count pointer 8 3
    (.const 32) (.const 8) arguments (by decide) (by decide) (Or.inr (Or.inl width)) heap facts.1 facts.2 updatedSafe ticks
  obtain ⟨_,headerDomain,wordDomain,byteDomain⟩ := htabNew_heap_domains_of_safe_plan state pointer (32 : BitVec 64) 8 pointerBound safe valid.journalWorld.heapDomain
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (32 : BitVec 64)))).update (ofString "cap",.val (.word (8 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word (32 : BitVec 64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cap" ≠ ofString "key_len" from by decide]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word (8 : BitVec 64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyPost,body,_⟩ := evaluate_source_htabNew_before_header_of_safe_plan entry pointer (32 : BitVec 64) 8 valid.journalWorld.code
    (by change 15 ≤ state.clock - 1; omega) heap pointerBound facts.1 safe keyLocal capLocal headerDomain wordDomain byteDomain
  have installed : state.code.lookup (ofString "htab_new") =
      some ([(ofString "key_len",.one),(ofString "cap",.one)],sourceFunctionBody Guest.guestFn_htab_new,.one) := by
    rw [valid.journalWorld.code]; exact originalRuntimeCode_htabNew_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    (sourceFunctionBody Guest.guestFn_htab_new) (32 : BitVec 64) 8 (by decide) installed
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 32,.const 8] =
      some [.val (.word (32 : BitVec 64)),.val (.word (8 : BitVec 64))] := rfl
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word pointer))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have discarded := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_new") [.const 32,.const 8]
    [.val (.word (32 : BitVec 64)),.val (.word (8 : BitVec 64))] (sourceFunctionBody Guest.guestFn_htab_new) callee .one (.val (.word pointer)) bodyPost args lookup (by omega) body shapeOk
  have same : post = {bodyPost with locals := state.locals} := congrArg Prod.snd (run.symm.trans discarded)
  have assignable : isValidValueHOLExact state.toExact .local name (.val (.word pointer)) = true := by
    simp [isValidValueHOLExact,lookupKvarHOLExact,localWord,shapeOfHOLExact,shapeEqHOL]
  have assigned := evaluateHOLFiniteState_call_return_set_kvar state .local name none (ofString "htab_new") [.const 32,.const 8]
    [.val (.word (32 : BitVec 64)),.val (.word (8 : BitVec 64))] (sourceFunctionBody Guest.guestFn_htab_new) callee .one (.val (.word pointer)) bodyPost args lookup (by omega) body shapeOk assignable
  rw [← same] at assigned
  refine ⟨setVarHOLFinite name (.val (.word pointer)) post,assigned,postValid.after_read rfl rfl rfl rfl rfl,cost,remaining,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · change post.globals.lookup _ = _
    rw [width] at heapNext
    exact heapNext

#print axioms TransactionRegistryWorld.new_storage_table_local_of_safe_plan
end InitECandidate.Runtime
