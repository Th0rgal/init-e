import InitECandidate.Runtime.HtrWithdrawalCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.HtrWithdrawalSource
import InitECandidate.Runtime.MerkleMarkedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrWithdrawal_marked_suffix : MarkedHeapReturn (ofString "mark") (htrWithdrawalAt 1) := by
  rw [source_htrWithdrawal_alloc]
  apply MarkedHeapReturn.decCall _ _ _ _ (by decide)
  rw [source_htrWithdrawal_u64_first]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrWithdrawal_u64_second]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrWithdrawal_vector]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrWithdrawal_u64_third]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_htrWithdrawal_merkle]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  exact MarkedHeapReturn.finish

theorem htrWithdrawal_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_withdrawal) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrWithdrawalAt 0) = _ at run
  rw [source_htrWithdrawal_mark] at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (htrWithdrawalAt 1) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (htrWithdrawalAt 1)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (htrWithdrawalAt 1) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := htrWithdrawal_marked_suffix.returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

theorem htrWithdrawal_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_withdrawal") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_withdrawal") =
      some ([(ofString "w",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_withdrawal,.one) := by
    rw [code]
    exact originalRuntimeCode_htrWithdrawal_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htr_withdrawal") (ofString "w")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_withdrawal) pointer out
    (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_withdrawal")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_withdrawal) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "w",.val (.word pointer))).update (ofString "out",.val (.word out)))
  exact htrWithdrawal_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms htrWithdrawal_call_normal_heap
#print axioms htrWithdrawal_marked_suffix
#print axioms htrWithdrawal_body_returned_heap
end InitECandidate.Runtime
