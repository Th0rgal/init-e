import InitECandidate.Runtime.HtrPlistChunksCallBound
import InitECandidate.Runtime.ProgressiveReturnedHeap
import InitECandidate.Runtime.MixInLengthGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrPlistChunks_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (roots n out heap : BitVec 64) (value : ValueHOL 64)
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_plist_chunks) =
      (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (.seq
    (.call (some (none,none)) (ofString "merkleize_progressive")
      [.var .local (ofString "roots"),.var .local (ofString "n"),.var .local (ofString "out")])
    (.seq (.call (some (none,none)) (ofString "mix_in_length")
      [.var .local (ofString "out"),.var .local (ofString "len"),.var .local (ofString "out")])
      (.return (.const 0)))) = _ at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have restored := progressive_call_normal_heap state middle _ roots n out heap
    (by simp [evalListHOLExact,evalHOLExact,hr,hn,ho]) code hh normal
  have meta' := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "merkleize_progressive")
      [.var .local (ofString "roots"),.var .local (ofString "n"),.var .local (ofString "out")])
  rw [normal] at meta'
  have frame := originalGlobalsFrame_sequence _ _
    (mixInLength_call_globals_frame [.var .local (ofString "out"),.var .local (ofString "len"),.var .local (ofString "out")])
    (originalGlobalsFrame_leaf (.return (.const 0)) (by intro watched; rfl)) middle (meta'.1.trans code)
  rw [tail] at frame
  rw [frame]
  exact restored

#print axioms htrPlistChunks_body_returned_heap
end InitECandidate.Runtime
