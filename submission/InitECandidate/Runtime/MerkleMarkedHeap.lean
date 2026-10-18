import InitECandidate.Runtime.MarkedHeapReturn
import InitECandidate.Runtime.MerkleizeBodyBound
import InitECandidate.Runtime.HeapMarkCall
import InitECandidate.Runtime.PanDecCallReturnedNonzeroClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem merkleize_marked_suffix : MarkedHeapReturn (ofString "mark") (merkleizeAt 5) := by
  rw [source_merkleSize_declaration]
  apply MarkedHeapReturn.dec _ _ _ (by decide)
  rw [source_merkleAllocation]
  apply MarkedHeapReturn.decCall _ _ _ _ (by decide)
  rw [source_merkleCopy]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_merkleZero]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_merkleCur_declaration]
  apply MarkedHeapReturn.dec _ _ _ (by decide)
  rw [source_merkleLevels]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_merkleDepth_declaration]
  apply MarkedHeapReturn.dec _ _ _ (by decide)
  rw [source_merklePadding]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  rw [source_merkleFinish]
  apply MarkedHeapReturn.seq _ (by decide) (by decide)
  exact MarkedHeapReturn.finish

/-- A returned positive-count path restores exactly the frontier read by the
actual heap_mark call, regardless of intermediate allocation/global effects. -/
theorem merklePositive_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (merkleizeAt 4) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [source_merkleMark] at run
  have ticks := evaluate_decCall_returned_nonzero_clock state post (ofString "mark") (ofString "heap_mark")
    .one [] (merkleizeAt 5) value run
  obtain ⟨ready,_,_,_,_,_,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code atHeap ticks
  rw [declaration (ofString "mark") (merkleizeAt 5)] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready)
      (merkleizeAt 5) with
  | mk result output =>
    rw [bodyRun] at run
    have resultEq := (Prod.mk.inj run).1
    dsimp only at resultEq
    subst result
    have restored := merkleize_marked_suffix.returned
      (setVarHOLFinite (ofString "mark") (.val (.word heap)) ready) output heap value (installed.trans code)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
    have globals : post.globals = output.globals := by rw [← (Prod.mk.inj run).2]
    rw [globals]
    exact restored

#print axioms merkleize_marked_suffix
#print axioms merklePositive_returned_heap
end InitECandidate.Runtime
