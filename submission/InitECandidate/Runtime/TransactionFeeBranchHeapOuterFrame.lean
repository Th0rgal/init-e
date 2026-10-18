import InitECandidate.Runtime.TransactionFeeDynamicHeapOuterFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem legacy_budget {cost clock : Nat} (h : 2 * cost ≤ clock) : cost ≤ clock := by omega

private theorem double_consumption {a b c : Nat} (h : a ≤ b+c) : a ≤ b+2*c := by omega

theorem transaction_fee_branch_normal_heap_outer_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx : BitVec 64)
    (array index input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (insideNext : (index + 1).toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : 2 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + 112 + 24 < array.toNat)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state transactionFeeBranch = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
      RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
      ∃ advance : BitVec 64, (advance = 1 ∨ advance = 2) ∧
        post.locals.lookup (ofString "k") = some (.val (.word (index + advance))) ∧
        state.clock ≤ post.clock + 2 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) := by
  unfold transactionFeeBranch at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · obtain ⟨slices,outer,globals,indexPost,consumed⟩ := transaction_fee_dynamic_normal_heap_outer_frame state post tx
        array index input inputLength scratch frame count ceiling inputLimit arrayLocal indexLocal valid inside insideNext
        inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayFits arrayAbove txLocal before
        outerArray outerCount outerInput outerLength outerValid outerFits outerAbove beforeTx run
      exact ⟨slices,outer,globals,2,Or.inr rfl,indexPost,consumed⟩
    · obtain ⟨slices,outer,globals,indexPost,consumed⟩ := transaction_fee_legacy_normal_heap_outer_frame state post tx
        array index input inputLength scratch frame count ceiling inputLimit arrayLocal indexLocal valid inside
        inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (legacy_budget budget) arrayFits arrayAbove txLocal
        (by omega) outerArray outerCount outerInput outerLength outerValid outerFits outerAbove beforeTx run
      exact ⟨slices,outer,globals,1,Or.inl rfl,indexPost,double_consumption consumed⟩
  · cases run

#print axioms transaction_fee_branch_normal_heap_outer_frame
end InitECandidate.Runtime
