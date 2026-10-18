import InitECandidate.Runtime.HtrPcontainerCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.HtrPcontainerSource
import InitECandidate.Runtime.MerkleMarkedHeap
import InitECandidate.Runtime.SemanticMarkedHeapReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrPcontainer_mask_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) :
    (evaluateHOLFiniteState state
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) htrPcontainerMaskBody)).1 ≠
      some (.returned value) := by
  apply (evaluate_while_terminal_control _ _ ?_ state).2.2 value
  intro current returnedValue
  rw [source_htrPcontainer_mask_body,evaluateHOLFiniteState_seq_line780]
  have first : (evaluateHOLFiniteState current htrPcontainerMaskStore).1 = none ∨
      (evaluateHOLFiniteState current htrPcontainerMaskStore).1 = some .error :=
    (evaluate_storeByte_control_frame current _ _).1
  cases stored : evaluateHOLFiniteState current htrPcontainerMaskStore with
  | mk result middle =>
    rw [stored] at first
    rcases first with normal | error
    · dsimp only at normal
      subst result
      exact evaluate_noDirectReturnWhile _ (by decide) middle returnedValue
    · dsimp only at error
      subst result
      simp

theorem htrPcontainer_marked_suffix : SemanticMarkedHeapReturn (ofString "mark") (htrPcontainerAt 1) := by
  rw [source_htrPcontainer_alloc]
  apply SemanticMarkedHeapReturn.decCall _ _ _ _ (by decide)
  rw [source_htrPcontainer_progressive]
  apply SemanticMarkedHeapReturn.seq _ (by decide) (by
    intro F state value
    exact evaluate_noDirectReturnWhile _ (by decide) state value)
  rw [source_htrPcontainer_act]
  apply SemanticMarkedHeapReturn.dec _ _ _ (by decide)
  rw [source_htrPcontainer_zero]
  apply SemanticMarkedHeapReturn.seq _ (by decide) (by
    intro F state value
    exact evaluate_noDirectReturnWhile _ (by decide) state value)
  rw [source_htrPcontainer_mask]
  apply SemanticMarkedHeapReturn.dec _ _ _ (by decide)
  apply SemanticMarkedHeapReturn.seq _ (by decide) (by
    intro F state value
    exact htrPcontainer_mask_no_return state value)
  rw [source_htrPcontainer_finish]
  apply SemanticMarkedHeapReturn.seq _ (by decide) (by
    intro F state value
    exact evaluate_noDirectReturnWhile _ (by decide) state value)
  exact SemanticMarkedHeapReturn.finish

theorem htrPcontainer_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_pcontainer) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrPcontainerAt 0) = _ at run
  rw [source_htrPcontainer_mark] at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (htrPcontainerAt 1) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (htrPcontainerAt 1)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (htrPcontainerAt 1) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := htrPcontainer_marked_suffix.returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

theorem htrPcontainer_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_pcontainer") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_pcontainer") =
      some ([(ofString "ch",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_pcontainer,.one) := by
    rw [code]
    exact originalRuntimeCode_htrPcontainer_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htr_pcontainer") (ofString "ch") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_pcontainer) pointer n out
    (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_pcontainer")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_pcontainer) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "ch",.val (.word pointer))).update
      (ofString "n",.val (.word n))).update (ofString "out",.val (.word out)))
  exact htrPcontainer_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms htrPcontainer_mask_no_return
#print axioms htrPcontainer_call_normal_heap
#print axioms htrPcontainer_marked_suffix
#print axioms htrPcontainer_body_returned_heap
end InitECandidate.Runtime
