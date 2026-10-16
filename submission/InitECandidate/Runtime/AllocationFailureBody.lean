import InitECandidate.Runtime.AllocationFailureTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original allocator body on an excessive request, including its
heap-pointer declaration and restoration of that local's scope. -/
theorem evaluate_source_alloc_request_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_alloc) = (result,post) ∧
      result ≠ none ∧ post.clock = state.clock - 1 := by
  let entered := setVarHOLFinite (ofString "p") (.val (.word pointer)) state
  have p : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have different : ofString "p" ≠ ofString "n" := by decide
  have n : entered.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,sizeLocal]
  obtain ⟨_,ticks,terminal⟩ := evaluate_allocationAfterPointer_failure entered pointer size code p n request
  let output := evaluateHOLFiniteState entered allocationAfterPointer
  refine ⟨output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
    (ofString "p",state.locals.lookup (ofString "p")))},?_,terminal,ticks⟩
  rw [source_alloc_body,evaluateHOLFiniteState_dec_total]
  dsimp only
  have initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.var .global (ofString "heap_ptr")) =
      some (.val (.word pointer)) := heap
  rw [initial]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word pointer))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk]

#print axioms evaluate_source_alloc_request_failure
end InitECandidate.Runtime
