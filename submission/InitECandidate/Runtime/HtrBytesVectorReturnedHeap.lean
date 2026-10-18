import InitECandidate.Runtime.HtrBytesVectorCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.HtrBytesVectorBodyBound
import InitECandidate.Runtime.MerkleMarkedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrBytesVectorLong_marked_suffix : MarkedHeapReturn (ofString "mark") (htrBytesVectorLongAt 1) := by
  rw [source_htrBytesVectorLong_pack]
  apply MarkedHeapReturn.decCall _ _ _ _ (by decide)
  rw [source_htrBytesVectorLong_tail]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  exact MarkedHeapReturn.finish

theorem htrBytesVectorLong_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (htrBytesVectorLongAt 0) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [source_htrBytesVectorLong_mark] at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (htrBytesVectorLongAt 1) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (htrBytesVectorLongAt 1)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (htrBytesVectorLongAt 1) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := htrBytesVectorLong_marked_suffix.returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

theorem htrBytesVector_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_bytes_vector) =
      (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [source_htrBytesVector_body,evaluateHOLFiniteState_seq_line780] at run
  have frame := htrBytesVector_check_globals state code
  have meta' := evaluateHOLFiniteState_metadata state htrBytesVectorCheck
  cases checked : evaluateHOLFiniteState state htrBytesVectorCheck with
  | mk result middle =>
    rw [checked] at run frame meta'
    cases result with
    | none =>
      exact htrBytesVectorLong_body_returned_heap middle post heap value (meta'.1.trans code)
        (by rw [frame]; exact hh) run
    | some result =>
      have equal := (Prod.mk.inj run).2
      rw [← equal,frame]
      exact hh

theorem htrBytesVector_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_bytes_vector") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_bytes_vector,.one) := by
    rw [code]
    exact originalRuntimeCode_htrBytesVector_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htr_bytes_vector") (ofString "p") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_bytes_vector) pointer n out
    (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_bytes_vector")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_bytes_vector) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "n",.val (.word n))).update (ofString "out",.val (.word out)))
  exact htrBytesVector_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms htrBytesVector_body_returned_heap
#print axioms htrBytesVector_call_normal_heap
#print axioms htrBytesVectorLong_marked_suffix
#print axioms htrBytesVectorLong_body_returned_heap
end InitECandidate.Runtime
