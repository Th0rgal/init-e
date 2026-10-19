import InitECandidate.Runtime.DecodeStepLeafBranchReturnedHeap
import InitECandidate.Runtime.DecodeStepScratchRecordFrame
import InitECandidate.Runtime.DecodeStepPathCompletedWorkspace
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_path_returned_heap_contract {F : Type}
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
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepCompactContinuation = (some (.returned value),post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      heap.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat%8=0 ∧
      ∀ watched : BitVec 64, ceiling ≤ watched.toNat → watched.toNat < heap.toNat →
        post.memory watched = s.memory watched := by
  by_cases zero : leaf=0
  · subst leaf
    rw [evaluate_decodeStep_extension_dispatch s nibs count atPath] at run
    rw [source_decodeStep_extension_suffix] at run
    obtain ⟨next,normal,tailRun⟩ := seq_returned_of_nonreturning_first
      (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
    have same := mpt_fail_guard_normal_state s next _ 7 code normal
    subst next
    obtain ⟨heapKept,memory⟩ := decode_step_extension_record_returned_upper_frame s post scratch frame
      array pointer length nibs count 0 atArray atPointer atLength atPath scratchGlobal frameGlobal orderedFrame
      code (by omega) value tailRun
    exact ⟨heap,heapKept.trans atHeap,le_refl _,heapBound,aligned,
      fun watched above before => memory watched (by omega)⟩
  · rw [evaluate_decode_step_leaf_dispatch s nibs count leaf zero atPath] at run
    obtain ⟨heapPost,growth,capped,finishAligned,memory⟩ := decode_step_leaf_branch_returned_heap_contract
      s post array slicePointer sliceLength scratch frame pointer length heap nibs count leaf ceiling inputLimit
      atArray slice noWrap lengthBound limitBound atPointer atLength atPath atHeap heapBound scratchGlobal frameGlobal
      code orderedFrame framePositive scratchBelow arena (by omega) value run
    exact ⟨allocationEnd heap 64,heapPost,growth,capped,finishAligned,memory⟩

#print axioms decode_step_path_returned_heap_contract
end InitECandidate.Runtime
