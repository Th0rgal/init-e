import InitECandidate.Runtime.HtrRequestsCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.MerkleMarkedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrRequests_marked_suffix : MarkedHeapReturn (ofString "mark") (htrRequestsAt 1) := by
  rw [source_htrRequests_alloc]
  apply MarkedHeapReturn.decCall _ _ _ _ (by decide)
  rw [source_htrRequests_list_0]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrRequests_list_1]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrRequests_list_2]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrRequests_list_3]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrRequests_list_4]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrRequests_hash]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  exact MarkedHeapReturn.finish

theorem htrRequests_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_requests) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrRequestsAt 0) = _ at run
  rw [source_htrRequests_mark] at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (htrRequestsAt 1) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (htrRequestsAt 1)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (htrRequestsAt 1) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := htrRequests_marked_suffix.returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

theorem htrRequests_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_requests") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have lookup := htrRequests_installed state pointer out code
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_requests")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_requests) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "rq",.val (.word pointer))).update (ofString "out",.val (.word out)))
  exact htrRequests_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms htrRequests_marked_suffix
#print axioms htrRequests_body_returned_heap
#print axioms htrRequests_call_normal_heap
end InitECandidate.Runtime
