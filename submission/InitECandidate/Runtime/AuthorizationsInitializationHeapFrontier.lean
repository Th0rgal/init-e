import InitECandidate.Runtime.AuthorizationsInitializationHeap
import InitECandidate.Runtime.AuthorizationsInitializationHeapBound
import InitECandidate.Runtime.AuthorizationsLoopReturnHeapFrontier
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsLoopHeapWitness
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual index scope retains traversal output memory and global contracts. -/
theorem authorization_initialized_returned_heap_frontier {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame heap : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (heapBound : heap.toNat ≤ 33806089496) (heapAligned : heap.toNat % 8 = 0)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heap.toNat)
    (recordsBeforeHeap : records.toNat + count.toNat * 120 ≤ heap.toNat)
    (heapAbove : ceiling ≤ heap.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 16 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : count.toNat *
      (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state authorizationInitialized = (some (.returned value),post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat = heap.toNat + 96 * count.toNat ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 := by
  let initial := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have atList : initial.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "lst" by decide] using listLocal
  have atRecords : initial.locals.lookup (ofString "recs") = some (.val (.word records)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "recs" by decide] using recordsLocal
  have atIndex : initial.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have initialSlices : RlpSliceInputPrefix initial array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,entry⟩ := slices slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame state initial array slot p n input inputLength entry rfl rfl rfl⟩
  let valid : AuthorizationsHeapLoopWitness initial array count records input inputLength scratch frame ceiling :=
    ⟨0,heap,atList,atRecords,atIndex,by simp,initialSlices,scratchGlobal,frameGlobal,heapGlobal,code,arena,
      heapArena,heapBound,heapAligned,inputBeforeHeap,recordsBeforeHeap,heapAbove⟩
  rw [source_authorization_initialized] at run
  obtain ⟨output,bodyRun,restored⟩ := evaluate_dec_word_result_scope state post (ofString "i") (.const 0) 0 authorizationLoopAndReturn
    (some (.returned value)) (by rfl) run
  have ticks : (count.toNat - valid.index.toNat) * (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ≤ initial.clock := by
    change (count.toNat - 0) * _ ≤ state.clock
    simpa only [Nat.sub_zero] using budget
  have retained := authorization_loop_returned_heap_frontier initial output array count records input inputLength scratch frame ceiling inputLimit
    valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayFits arrayAbove arrayBeforeRecords countLimit inputBeforeFrame ticks value bodyRun
  rw [restored]
  obtain ⟨nextHeap,binding,growth,bounded,aligned⟩ := retained
  refine ⟨nextHeap,binding,?_,bounded,aligned⟩
  change nextHeap.toNat = heap.toNat + 96 * (count.toNat - 0) at growth
  simpa only [Nat.sub_zero] using growth

#print axioms authorization_initialized_returned_heap_frontier
end InitECandidate.Runtime
