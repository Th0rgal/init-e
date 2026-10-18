import InitECandidate.Runtime.TransactionBlobBodyBound
import InitECandidate.Runtime.PanConditionalSkipBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original type-3 conditional covers blob execution, skipping, and failed guards. -/
theorem evaluate_transaction_blob_branch_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : (index + 1#64).toNat < count.toNat)
    (middleInside : index.toNat < count.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + 224 + 24 < array.toNat)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (heapBeforeFrame : heapPointer.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (budget : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionBlobBranch
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have bound := evaluate_transaction_blob_body_bounded state array count index tx input inputLength scratch frame heapPointer ceiling inputLimit
    arrayLocal indexLocal valid inside middleInside txLocal before arrayBelow inputBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heap heapBound countLimit heapArena inputBeforeHeap heapBeforeFrame budget
  rw [source_transaction_blob_branch]
  have checked := evaluate_conditional_skip_bounded state
    (.cmp .equal (.var .local (ofString "t")) (.const 3)) transactionBlobBody
    ((inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost inputLength.toNat)
    ⟨by simpa only [Nat.add_assoc] using bound.1,bound.2.1,bound.2.2⟩
  simpa only [Nat.add_assoc] using checked

#print axioms evaluate_transaction_blob_branch_bounded
end InitECandidate.Runtime
