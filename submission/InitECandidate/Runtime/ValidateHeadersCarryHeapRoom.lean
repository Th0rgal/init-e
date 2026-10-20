import InitECandidate.Runtime.ValidateHeadersActualIterationGrowth
import InitECandidate.Runtime.ValidateHeadersParentReaches
import InitECandidate.Runtime.HtabTxBridge
/-!
The wiring lemma: the carry itself entails the iteration's heap room.

The retained `count.toNat ≤ 23`, the allocation equation `record = allocationEnd heapStart
(count*16)`, the heap binding and the record's room under the cap are all conjuncts of
`parentRecordCarry`; the record's alignment is `allocationEnd_aligned`.  So
`parentRecordCarry` plus the caller's own 624-byte room yields `nextHeap < heapStart + 624` with
no count hypothesis and no allocation identity assumption.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- **Growth from the carry.**  The decode call's carry, together with the caller's heap room,
bounds the heap after the iteration by `heapStart + headerCarryRoom`. -/
theorem validate_headers_carry_heap_room {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (heapStart pointer length : BitVec 64) (ceiling : Nat)
    (older outerInput outerLength olderCount : BitVec 64)
    (heapCapped : heapStart.toNat + headerCarryRoom ≤ 33806089496)
    (carried : parentRecordCarry s next heapStart pointer length ceiling older outerInput outerLength
      olderCount) :
    ∃ record : BitVec 64, next.locals.lookup (ofString "h") = some (.val (.word record)) ∧
      ∃ nextHeap : BitVec 64, next.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
        nextHeap.toNat < heapStart.toNat + headerCarryRoom := by
  obtain ⟨value,post,count,record,rooted,run,shape,valueEq,recordEq,nextEq,hLocal,rootMem,rootHere,
    domain,code,heapPost,scratchPost,framePost,before,room,window,outerRetained,countBound⟩ := carried
  have recordAligned : record.toNat % 8 = 0 := by
    rw [recordEq]
    exact allocationEnd_aligned heapStart (count * 16)
  have heapAt := heapPost
  refine ⟨record,hLocal,allocationEnd (allocationEnd heapStart (count * 16)) 248,heapAt,?_⟩
  exact validate_headers_actual_iteration_growth heapStart count record
    (allocationEnd (allocationEnd heapStart (count * 16)) 248) heapCapped countBound recordEq (by rw [← recordEq])
    recordAligned room

#print axioms validate_headers_carry_heap_room
end InitECandidate.Runtime
