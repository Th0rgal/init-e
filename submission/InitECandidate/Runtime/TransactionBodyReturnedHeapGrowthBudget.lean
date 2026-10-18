import InitECandidate.Runtime.TransactionBodyReturnedHeapGrowth
import InitECandidate.Runtime.TransactionBodyBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem decoder_budget_expanded (n clock : Nat) (budget : transactionAllocationSuffixCost n ≤ clock) :
    402 + ((n * ((2 * n + 1) * 15 + 19) + 92635) + (n * ((2 * n + 1) * 15 + 19) + n * 12 + 4 + (n * ((2 * n + 1) * 15 + 19) + 92643 + (n * ((2 * n + 1) * 15 + 19) + 92668 + (2 * (n * ((2 * n + 1) * 15 + 19) + 92668) + (n * ((2 * n + 1) * 15 + 19) + 92643 + (n * ((2 * n + 1) * 15 + 19) + 92634 + (n * ((2 * n + 1) * 15 + 19) + 92668 + (n * ((2 * n + 1) * 15 + 19) + 92634 + transactionTypedSignatureCost n))))))))) ≤ clock := by
  simp only [transactionAllocationSuffixCost,transactionMemzeroSuffixCost,transactionTypedSuffixCost,
      transactionListSuffixCost,transactionChainIdSuffixCost,transactionNonceSuffixCost,transactionFeeDynamicSuffixCost,
      transactionGasSuffixCost,transactionToSuffixCost,transactionValueSuffixCost,transactionDataSequenceCost,Nat.add_assoc] at budget ⊢
  omega

theorem transaction_body_returned_heap_growth_budget {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : transactionAllocationSuffixCost length.toNat ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (tx : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (allocationBeforeFrame : tx.toNat + 400 ≤ frame.toNat)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (fieldsBeforeFrame : tx.toNat + 400 + length.toNat * 16 ≤ frame.toNat)
    (inputBeforeTx : pointer.toNat + length.toNat ≤ tx.toNat)
    (heapSpace : tx.toNat + 400 + length.toNat * 16 ≤ 33806089496)
    (suffixCountLimit : inputLimit * 120 < 2^64)
    (suffixSpace : tx.toNat + 400 + length.toNat * 56 + (length.toNat * 48 + 46) * length.toNat + length.toNat * 296 + 7 ≤ frame.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      tx.toNat ≤ nextHeap.toNat ∧
      nextHeap.toNat ≤ tx.toNat + 400 + length.toNat * 56 + (length.toNat * 48 + 46) * length.toNat + length.toNat * 280 ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  exact transaction_body_returned_heap_growth state post pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (transactionTypedSignatureCost length.toNat)
    (decoder_budget_expanded length.toNat state.clock budget)
    array count input inputLength valid before tx heap small aligned txArena countLimit heapArena allocationBeforeFrame beforeTx fieldsBeforeFrame
    inputBeforeTx heapSpace suffixCountLimit suffixSpace (Nat.le_refl _) value run

#print axioms transaction_body_returned_heap_growth_budget
end InitECandidate.Runtime
