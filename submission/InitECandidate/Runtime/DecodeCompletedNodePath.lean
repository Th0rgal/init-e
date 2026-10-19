import InitECandidate.Runtime.DecodeCompletedNodeLeafBranch
import InitECandidate.Runtime.DecodeStepScratchRecordFrame
import InitECandidate.Runtime.DecodeStepPathCompletedWorkspace
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_path_completed_node {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (array slicePointer sliceLength scratch frame pointer length heap nibs count leaf : BitVec 64)
    (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (slice : RlpSliceEntry s array 1 slicePointer sliceLength)
    (noWrap : slicePointer.toNat + sliceLength.toNat < 2^64)
    (lengthBound : sliceLength.toNat ≤ inputLimit) (limitBound : inputLimit+9 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atPath : s.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat%8=0)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : sliceLength.toNat*((2*sliceLength.toNat+1)*15+19)+92637 ≤ s.clock)
    (value : ValueHOL 64) (node : BitVec 64)
    (completed : value=.rStruct [.val (.word (0#64)),.val (.word node)])
    (run : evaluateHOLFiniteState s decodeStepCompactContinuation = (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
  by_cases zero : leaf=0
  · subst leaf
    rw [evaluate_decodeStep_extension_dispatch s nibs count atPath] at run
    obtain ⟨record,same⟩ := decode_step_extension_returned_tag s post value run
    rw [completed] at same
    have firstEq := (List.cons.inj (ValueHOL.rStruct.inj same)).1
    have impossible : (0 : BitVec 64)=1 := HolWordLab.word.inj (ValueHOL.val.inj firstEq)
    exact False.elim ((by decide : (0 : BitVec 64)≠1) impossible)
  · rw [evaluate_decode_step_leaf_dispatch s nibs count leaf zero atPath] at run
    exact decode_step_leaf_branch_completed_node s post array slicePointer sliceLength scratch frame pointer length heap
      nibs count leaf ceiling inputLimit atArray slice noWrap lengthBound limitBound atPointer atLength atPath atHeap heapBound
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega) value node completed run

#print axioms decode_step_path_completed_node
end InitECandidate.Runtime
