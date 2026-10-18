import InitECandidate.Runtime.HtrPbytesCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.HtrPbytesBound
import InitECandidate.Runtime.MerkleMarkedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrPbytes_marked_suffix : MarkedHeapReturn (ofString "mark") (htrPbytesAt 1) := by
  rw [source_htrPbytes_pack]
  apply MarkedHeapReturn.decCall _ _ _ _ (by decide)
  rw [source_htrPbytes_tail]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  exact MarkedHeapReturn.finish

theorem htrPbytes_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_pbytes) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrPbytesAt 0) = _ at run
  rw [source_htrPbytes_mark] at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (htrPbytesAt 1) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (htrPbytesAt 1)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (htrPbytesAt 1) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := htrPbytes_marked_suffix.returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

theorem htrPbytes_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_pbytes") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_pbytes") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_pbytes,.one) := by
    rw [code]
    exact originalRuntimeCode_htrPbytes_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htr_pbytes") (ofString "p") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_pbytes) pointer n out
    (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_pbytes")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_pbytes) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "n",.val (.word n))).update (ofString "out",.val (.word out)))
  exact htrPbytes_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms htrPbytes_call_normal_heap
#print axioms htrPbytes_marked_suffix
#print axioms htrPbytes_body_returned_heap
end InitECandidate.Runtime
