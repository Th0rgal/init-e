import InitECandidate.Runtime.HtrPayloadSource
import InitECandidate.Runtime.OriginalHtrPayloadCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.MerkleMarkedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem source_htrPayload_mark : htrPayloadAt 1 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrPayloadAt 2) := by rfl

/-- Every returned path through the original payload suffix reaches the
outer release; the nested transaction and withdrawal marks keep it intact. -/
theorem htrPayload_marked_suffix : MarkedHeapReturn (ofString "mark") (htrPayloadAt 2) := by
  repeat first
    | exact MarkedHeapReturn.finish
    | apply MarkedHeapReturn.seq _ (by decide) (by decide)
    | apply MarkedHeapReturn.decCall _ _ _ _ (by decide)
    | apply MarkedHeapReturn.dec _ _ _ (by decide)

theorem htrPayload_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_payload) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrPayloadAt 0) = _ at run
  have rawSource : htrPayloadAt 0 = .dec (ofString "raw") .one
      (.load .one (.op .add [.var .local (ofString "pl"),.const 0])) (htrPayloadAt 1) := by rfl
  rw [rawSource] at run
  obtain ⟨raw,final,_,rawRun,postEq⟩ := evaluate_dec_returned_scope state post (ofString "raw") .one _ _ value run
  have core (state post : PanSemStateFiniteExact 64 F)
      (code : state.code = originalRuntimeCode)
      (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
      (run : evaluateHOLFiniteState state (htrPayloadAt 1) = (some (.returned value),post)) :
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
    rw [source_htrPayload_mark] at run
    have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
      .one [] (htrPayloadAt 2) value run
    obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
      evaluate_heapMark_call_and_declaration state heap code atHeap ticks
    rw [declaration (ofString "mark") (htrPayloadAt 2)] at run
    cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
        (htrPayloadAt 2) with
    | mk result output =>
      rw [bodyRun] at run
      have resultEq := (Prod.mk.inj run).1
      dsimp only at resultEq
      subst result
      have restored := htrPayload_marked_suffix.returned
        (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
        (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
      have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
      rw [globals]
      exact restored
  
  rw [postEq]
  exact core (setVarHOLFinite (ofString "raw") raw state) final code atHeap rawRun

theorem htrPayload_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_payload") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "htr_payload") (ofString "pl") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_payload) .one pointer out (by decide)
    (by rw [code]; exact originalRuntimeCode_htrPayload_lookup)
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_payload")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_payload) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "pl",.val (.word pointer))).update (ofString "out",.val (.word out)))
  exact htrPayload_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms htrPayload_call_normal_heap
#print axioms htrPayload_marked_suffix
#print axioms htrPayload_body_returned_heap
end InitECandidate.Runtime
