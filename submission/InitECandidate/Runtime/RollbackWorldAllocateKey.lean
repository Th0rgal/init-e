import InitECandidate.Runtime.RollbackWorldHeapAdvance
import InitECandidate.Runtime.RollbackWorldRead
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual saved-key allocation declaration reaches a reusable full world
at its new frontier and restores the old kc binding after the continuation. -/
theorem RollbackWorld.allocate_key {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (argument : ExpHOL 64) (pointer size : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer size).toNat ≤ 33806089496) :
    ∃ post, (∀ continuation, evaluateHOLFiniteState state (.decCall (ofString "kc") .one (ofString "alloc") [argument] continuation) =
      (let output := evaluateHOLFiniteState post continuation;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "kc",state.locals.lookup (ofString "kc"))}))) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post ∧
      post.locals.lookup (ofString "kc") = some (.val (.word pointer)) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HeapGlobalsFrame state post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) ∧
      post.locals = (setVarHOLFinite (ofString "kc") (.val (.word pointer)) state).locals := by
  obtain ⟨allocated,_,ticks,memory,locals,postCode,domain,_,endian,globals,decl⟩ :=
    evaluate_alloc_call_and_declaration state argument pointer size arguments code clock heap request finish
  have heapNext : allocated.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have frame : HeapGlobalsFrame state allocated := by
    intro watched different
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have covers := allocationEnd_covers pointer size (allocationGuard_sum_bound pointer size pointerBound request)
  obtain ⟨midWorld,midSep⟩ := world.advance_heap separated pointer (allocationEnd pointer size) heap heapNext (by omega) finish covers.2.2
    memory frame locals postCode domain endian
  let post := setVarHOLFinite (ofString "kc") (.val (.word pointer)) allocated
  have postWorld : RollbackWorld widths tables journal snapshot count post := midWorld.after_read rfl rfl rfl rfl rfl (by
    simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "kc" ≠ ofString "snap" from by decide])
  refine ⟨post,decl (ofString "kc"),postWorld,midSep.after_read rfl rfl rfl rfl rfl,?_,ticks,memory,postCode,domain,endian,frame,heapNext,?_⟩
  · simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp only [post,setVarHOLFinite,locals]

#print axioms RollbackWorld.allocate_key
end InitECandidate.Runtime
