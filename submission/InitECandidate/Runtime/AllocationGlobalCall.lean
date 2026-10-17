import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The assignment-form allocator call updates an existing word global with
its returned pointer and preserves all other globals except the heap frontier. -/
theorem evaluate_alloc_global_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer size oldValue : BitVec 64) (name : MlS)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (globalWord : state.globals.lookup name = some (.val (.word oldValue)))
    (different : name ≠ ofString "heap_ptr")
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer size).toNat ≤ 33806089496) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (some (.global,name),none)) (ofString "alloc") [argument]) = (none,ready) ∧
      ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧ ready.locals = state.locals ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.globals.lookup name = some (.val (.word pointer)) ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) ∧
      (∀ watched, watched ≠ name → watched ≠ ofString "heap_ptr" → ready.globals.lookup watched = state.globals.lookup watched) := by
  obtain ⟨post,run,ticks,memory,locals,postCode,domain,_,endian,globals,_⟩ :=
    evaluate_alloc_call_and_declaration state argument pointer size arguments code clock heapGlobal request finishBound
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyPost,body,_⟩ := evaluate_source_alloc_success entry pointer size heapGlobal sizeLocal request finishBound
  have installed : state.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) size installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word pointer))) .one = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  have discarded := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "alloc") [argument]
    [.val (.word size)] (sourceFunctionBody Guest.guestFn_alloc) callee .one (.val (.word pointer)) bodyPost arguments lookup clock body shapeOk
  have same : post = {bodyPost with locals := state.locals} := congrArg Prod.snd (run.symm.trans discarded)
  have valid : isValidValueHOLExact state.toExact .global name (.val (.word pointer)) = true := by
    simp [isValidValueHOLExact,lookupKvarHOLExact,globalWord,shapeOfHOLExact,shapeEqHOL]
  have assigned := evaluateHOLFiniteState_call_return_set_kvar state .global name none (ofString "alloc") [argument]
    [.val (.word size)] (sourceFunctionBody Guest.guestFn_alloc) callee .one (.val (.word pointer)) bodyPost arguments lookup clock body shapeOk valid
  rw [← same] at assigned
  refine ⟨setGlobalHOLFinite name (.val (.word pointer)) post,assigned,ticks,memory,locals,postCode,domain,endian,?_,?_,?_⟩
  · simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,globals]
  · intro watched notName notHeap
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notName,Ne.symm notHeap,globals]

#print axioms evaluate_alloc_global_call
end InitECandidate.Runtime
