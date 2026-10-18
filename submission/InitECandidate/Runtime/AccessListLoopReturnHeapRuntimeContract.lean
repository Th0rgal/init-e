import InitECandidate.Runtime.AccessListLoopHeapRuntimeContract
import InitECandidate.Runtime.AccessListLoopReturnedHeapResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returned traversal preserves the input array and exposes its final heap layout. -/
theorem access_loop_returned_heap_runtime_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessHeapLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (budget : (count.toNat - valid.index.toNat) *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state accessLoopAndReturn = (some (.returned value),post)) :
    value = .rStruct [.val (.word records),.val (.word count)] ∧
    ∃ heap : BitVec 64,
      RlpSliceInputPrefix post array input inputLength count.toNat ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      heap.toNat ≤ 33806089496 ∧ heap.toNat % 8 = 0 ∧
      input.toNat + inputLength.toNat ≤ heap.toNat ∧
      records.toNat + count.toNat * 24 ≤ heap.toNat := by
  obtain ⟨middle,loopRun,shape,restored⟩ := access_loop_returned_heap_result state post array count records input inputLength scratch frame
    ceiling inputLimit valid inputBound limitBound orderedFrame framePositive scratchBelow arrayAbove arrayBeforeRecords countLimit inputBeforeFrame budget value run
  obtain ⟨heap,_,_,_,slices,scratchPost,framePost,heapPost,heapBound,aligned,inputBefore,recordsBefore⟩ :=
    access_loop_normal_heap_runtime_contract state middle array count records input inputLength scratch frame ceiling inputLimit valid
      inputBound limitBound orderedFrame framePositive scratchBelow arrayAbove arrayBeforeRecords countLimit inputBeforeFrame budget loopRun
  rw [restored]
  refine ⟨shape,heap,?_,scratchPost,framePost,heapPost,heapBound,aligned,inputBefore,recordsBefore⟩
  intro slot inside
  obtain ⟨p,n,item⟩ := slices slot inside
  exact ⟨p,n,item.after_frame middle _ array slot p n input inputLength rfl rfl rfl⟩

#print axioms access_loop_returned_heap_runtime_contract
end InitECandidate.Runtime
