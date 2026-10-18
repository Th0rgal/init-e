import InitECandidate.Runtime.VersionedHashesSourceStepGuardedHeapGrowth
import InitECandidate.Runtime.TransactionCostMonotone
import InitECandidate.Runtime.TransactionHeapBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem versioned_hashes_uniform_source_step_guarded_heap_growth {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index wholeInput wholeLength vh cursor : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (input inputLength scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
    (slice : RlpSliceInputEntry state array index input inputLength wholeInput wholeLength)
    (wholeBound : wholeLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (heapWithin : tx.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : wholeInput.toNat + wholeLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ wholeInput.toNat))
    (inputBeforeArray : wholeInput.toNat + wholeLength.toNat ≤ tx.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionWrapperCallCost wholeLength.toNat ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state versionedHashesStep = (none,post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      tx.toNat ≤ nextHeap.toNat ∧
      nextHeap.toNat ≤ tx.toNat + transactionHeapGrowth wholeLength.toNat ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  have lengthBound := slice.length_bound state array index input inputLength wholeInput wholeLength
  have cost := transaction_wrapper_call_cost_mono inputLength.toNat wholeLength.toNat lengthBound
  have growth := transaction_heap_growth_mono inputLength.toNat wholeLength.toNat lengthBound
  obtain ⟨nextHeap,binding,lower,upper,heapBound,aligned,scratchFinal,frameFinal⟩ := versioned_hashes_source_step_normal_guarded_heap_growth state post
    array index wholeInput wholeLength vh cursor arrayLocal indexLocal vhLocal cursorLocal input inputLength scratch frame tx ceiling inputLimit
    slice wholeBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap heapWithin countLimit heapArena
    inputBeforeFrame inputBeforeArray txAligned (cost.trans budget)
    outerArray outerCount outerInput outerLength outerValid outerAbove beforeTx run
  have nestedGrowth : nextHeap.toNat ≤ tx.toNat + transactionHeapGrowth inputLength.toNat := by
    simpa only [transactionHeapGrowth,Nat.add_assoc] using upper
  exact ⟨nextHeap,binding,lower,nestedGrowth.trans (Nat.add_le_add_left growth _),heapBound,aligned,scratchFinal,frameFinal⟩

#print axioms versioned_hashes_uniform_source_step_guarded_heap_growth
end InitECandidate.Runtime
