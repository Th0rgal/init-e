import InitECandidate.Runtime.MerkleMarkedHeap
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleEmpty_branch_globals : OriginalGlobalsFrame merkleEmptyBranch := by
  rw [source_merkleEmpty_branch]
  exact originalGlobalsFrame_sequence _ _ (memcpy_call_globals_frame _)
    (originalGlobalsFrame_leaf _ (by intro watched; rfl))

theorem merkleEmpty_check_globals : OriginalGlobalsFrame merkleEmptyCheck := by
  rw [source_merkleEmpty_check]
  exact originalGlobalsFrame_conditional _ _ _ merkleEmpty_branch_globals
    (originalGlobalsFrame_leaf _ (by intro watched; rfl))

/-- Empty returns keep globals; every returning nonempty path restores its
saved heap mark. This property needs no input or current-heap size bound. -/
theorem merkleAfterTarget_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (merkleizeAt 3) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [source_merkleEmpty_sequence,evaluateHOLFiniteState_seq_line780] at run
  have frame := merkleEmpty_check_globals state code
  have meta' := evaluateHOLFiniteState_metadata state merkleEmptyCheck
  cases firstRun : evaluateHOLFiniteState state merkleEmptyCheck with
  | mk result middle =>
    rw [firstRun] at run frame meta'
    cases result with
    | none =>
      exact merklePositive_returned_heap middle post heap value (meta'.1.trans code)
        (by rw [frame]; exact atHeap) run
    | some result =>
      have equal := (Prod.mk.inj run).2
      rw [← equal,frame]
      exact atHeap

#print axioms merkleEmpty_branch_globals
#print axioms merkleEmpty_check_globals
#print axioms merkleAfterTarget_returned_heap
end InitECandidate.Runtime
