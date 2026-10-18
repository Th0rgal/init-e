import InitECandidate.Runtime.TransactionBodyHeapBound
import InitECandidate.Runtime.TransactionBodyAllocationFailureBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_transaction_body_guarded_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (input inputLength scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (noWrap : input.toNat + inputLength.toNat < 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (heapWithin : tx.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ tx.toNat)
    (heapAbove : ceiling ≤ tx.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionAllocationSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp)
    state.clock ≤ evaluated.2.clock + transactionAllocationSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases capacity : tx.toNat + 400 ≤ 33806089496
  · exact evaluate_transaction_body_heap_bounded state input inputLength scratch frame tx ceiling inputLimit pointerLocal lengthLocal noWrap inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap capacity countLimit heapArena inputBeforeFrame inputBeforeArray heapAbove txAligned budget
  · have request : ((33806089496 : BitVec 64) - tx).toNat < 400 := by
      rw [BitVec.toNat_sub_of_le (by change tx.toNat ≤ 33806089496; exact heapWithin)]
      change 33806089496 - tx.toNat < 400
      omega
    have minimum : 2 ≤ transactionAllocationSuffixCost inputLength.toNat := by
      simp only [transactionAllocationSuffixCost,transactionMemzeroSuffixCost]
      omega
    have bounded := transaction_body_allocation_failure_bounded state inputLength tx lengthLocal code heap request (Nat.le_trans minimum budget)
    exact ⟨Nat.le_trans bounded.1 (Nat.add_le_add_left minimum _),bounded.2⟩

#print axioms evaluate_transaction_body_guarded_heap_bounded
end InitECandidate.Runtime
