import InitECandidate.Runtime.HtrBytesListCallBound
import InitECandidate.Runtime.ProgressiveReturnedHeap
import InitECandidate.Runtime.MixInLengthGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrBytesList_tail_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (saved : state.locals.lookup (ofString "mark") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (htrBytesListAt 2) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [source_htrBytesList_tail] at run
  obtain ⟨middle,normal,rest⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have frame := evaluate_avoidsLocal_flowing (ofString "mark")
    (.call (some (none,none)) (ofString "merkleize")
      [.rfield 0 (.var .local (ofString "pk")),.rfield 1 (.var .local (ofString "pk")),
        .var .local (ofString "limit_chunks"),.var .local (ofString "out")]) rfl state
    (by rw [normal]; exact Or.inl rfl)
  have meta' := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "merkleize")
      [.rfield 0 (.var .local (ofString "pk")),.rfield 1 (.var .local (ofString "pk")),
        .var .local (ofString "limit_chunks"),.var .local (ofString "out")])
  rw [normal] at frame meta'
  obtain ⟨released,release,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) middle v) rest
  have atMark : middle.locals.lookup (ofString "mark") = some (.val (.word heap)) := frame.trans saved
  have releasedHeap := heapRelease_call_normal middle released (.var .local (ofString "mark")) heap
    (meta'.1.trans code) (by simp [evalListHOLExact,evalHOLExact,atMark]) release
  have releasedCode := evaluateHOLFiniteState_metadata middle
    (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
  rw [release] at releasedCode
  have globals := originalGlobalsFrame_sequence _ _
    (mixInLength_call_globals_frame [.var .local (ofString "out"),.var .local (ofString "n"),.var .local (ofString "out")])
    (originalGlobalsFrame_leaf (.return (.const 0)) (by intro watched; rfl)) released
    (releasedCode.1.trans (meta'.1.trans code))
  rw [tail] at globals
  rw [globals]
  exact releasedHeap

theorem htrBytesList_marked_suffix_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (saved : state.locals.lookup (ofString "mark") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (htrBytesListAt 1) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [source_htrBytesList_pack] at run
  obtain ⟨bound,ready,output,locals,installed,tail,globals⟩ := evaluate_decCall_returned_continuation state post
    (ofString "pk") (ofString "pack_bytes") (.comb [.one,.one]) _ (htrBytesListAt 2) value run
  have atMark : (setVarHOLFinite (ofString "pk") bound ready).locals.lookup (ofString "mark") = some (.val (.word heap)) := by
    simpa (config := {decide := true}) [setVarHOLFinite,locals,HolFiniteMapExact.lookup_update,FUPDATE] using saved
  rw [globals]
  exact htrBytesList_tail_returned_heap (setVarHOLFinite (ofString "pk") bound ready) output heap value
    (installed.trans code) atMark tail

theorem htrBytesList_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_bytes_list) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrBytesListAt 0) = _ at run
  rw [source_htrBytesList_mark] at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (htrBytesListAt 1) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (htrBytesListAt 1)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (htrBytesListAt 1) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := htrBytesList_marked_suffix_returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

theorem htrBytesList_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer n limit out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word limit),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bytes_list") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_bytes_list") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "limit_chunks",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_bytes_list,.one) := by
    rw [code]
    exact originalRuntimeCode_htr_bytes_list_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "htr_bytes_list") (ofString "p") (ofString "n")
    (ofString "limit_chunks") (ofString "out") (sourceFunctionBody Guest.guestFn_htr_bytes_list) pointer n limit out
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_bytes_list")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_bytes_list) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "n",.val (.word n))).update (ofString "limit_chunks",.val (.word limit))).update
      (ofString "out",.val (.word out)))
  exact htrBytesList_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms htrBytesList_tail_returned_heap
#print axioms htrBytesList_marked_suffix_returned
#print axioms htrBytesList_body_returned_heap
#print axioms htrBytesList_call_normal_heap
end InitECandidate.Runtime
