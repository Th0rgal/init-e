import InitECandidate.Runtime.HtrNewPayloadCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.MerkleMarkedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrNewPayload_marked_suffix : MarkedHeapReturn (ofString "mark") (htrNewPayloadAt 1) := by
  rw [source_htrNewPayload_alloc]
  apply MarkedHeapReturn.decCall _ _ _ _ (by decide)
  rw [source_htrNewPayload_payload]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrNewPayload_blobs]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrNewPayload_copy]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrNewPayload_requests]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrNewPayload_merkle]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  exact MarkedHeapReturn.finish

theorem htrNewPayload_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_new_payload_request) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrNewPayloadAt 0) = _ at run
  rw [source_htrNewPayload_mark] at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (htrNewPayloadAt 1) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (htrNewPayloadAt 1)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (htrNewPayloadAt 1) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := htrNewPayload_marked_suffix.returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

theorem htrNewPayload_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_new_payload_request") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "htr_new_payload_request") (ofString "si") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_new_payload_request) .one pointer out (by decide)
    (by rw [code]; exact originalRuntimeCode_htrNewPayload_lookup)
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_new_payload_request")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_new_payload_request) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "si",.val (.word pointer))).update (ofString "out",.val (.word out)))
  exact htrNewPayload_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms htrNewPayload_marked_suffix
#print axioms htrNewPayload_body_returned_heap
#print axioms htrNewPayload_call_normal_heap
end InitECandidate.Runtime
