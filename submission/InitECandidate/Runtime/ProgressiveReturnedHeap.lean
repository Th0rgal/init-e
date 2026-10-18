import InitECandidate.Runtime.ProgressiveCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.ProgressiveSuffixSource
import InitECandidate.Runtime.MerkleMarkedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem progressive_marked_suffix : MarkedHeapReturn (ofString "mark") (progressiveAt 1) := by
  rw [source_progressive_roots]
  apply MarkedHeapReturn.decCall _ _ _ _ (by decide)
  rw [source_progressive_acc]
  apply MarkedHeapReturn.decCall _ _ _ _ (by decide)
  rw [source_progressive_counters]
  apply MarkedHeapReturn.dec _ _ _ (by decide)
  apply MarkedHeapReturn.dec _ _ _ (by decide)
  apply MarkedHeapReturn.dec _ _ _ (by decide)
  rw [source_progressive_loop]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_progressive_zero]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_progressive_fold]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_progressive_finish]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  exact MarkedHeapReturn.finish

theorem progressive_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_merkleize_progressive) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (progressiveAt 0) = _ at run
  rw [source_progressive_mark] at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (progressiveAt 1) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (progressiveAt 1)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (progressiveAt 1) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := progressive_marked_suffix.returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

theorem progressive_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "merkleize_progressive") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "merkleize_progressive") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_merkleize_progressive,.one) := by
    rw [code]
    exact originalRuntimeCode_progressive_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "merkleize_progressive") (ofString "p") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_merkleize_progressive) pointer n out
    (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "merkleize_progressive")
    .one arguments _ (sourceFunctionBody Guest.guestFn_merkleize_progressive) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "n",.val (.word n))).update (ofString "out",.val (.word out)))
  exact progressive_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms progressive_call_normal_heap
#print axioms progressive_marked_suffix
#print axioms progressive_body_returned_heap
end InitECandidate.Runtime
