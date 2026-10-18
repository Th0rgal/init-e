import InitECandidate.Runtime.TransactionChainIdHeapOuterPrefix
import InitECandidate.Runtime.TransactionChainIdHeapFrame
import InitECandidate.Runtime.TransactionChainIdBound
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.TransactionChainIdIndexValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_chain_id_returned_heap_outer_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 0 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 ≤ state.clock)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (headerBefore : tx.toNat + 8 < array.toNat)
    (kind : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word 0)))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 17) = (some (.returned value),post)) :
    ∃ middle : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle (transactionAt 18) = (some (.returned value),post) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧
      RlpSliceInputPrefix middle outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, middle.globals.lookup watched = state.globals.lookup watched) ∧
      (∀ name, name ≠ ofString "w" → name ≠ ofString "k" → middle.locals.lookup name = state.locals.lookup name) ∧
      middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧
      state.clock ≤ middle.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643) ∧
      middle.clock ≤ state.clock ∧
      middle.locals.lookup (ofString "k") = some (.val (.word (if kind = 0 then 0 else 1))) := by
  have noReturn := evaluate_noDirectReturn transactionChainIdBranch (by rfl) state value
  have bounded := evaluate_transaction_chain_id_bounded state array input inputLength scratch frame count.toNat ceiling inputLimit
    arrayLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  have metadata := evaluateHOLFiniteState_metadata state transactionChainIdBranch
  rw [source_transaction_chain_id,evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state transactionChainIdBranch with
  | mk result middle =>
    rw [branchRun] at run noReturn bounded metadata
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      have retained := transaction_chain_id_normal_heap_frame state middle array input inputLength scratch frame count ceiling inputLimit
        arrayLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
        arrayFits arrayAbove tx txLocal headerBefore branchRun
      have outer := transaction_chain_id_normal_heap_outer_prefix state middle array input inputLength scratch frame count ceiling inputLimit
        arrayLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
        arrayFits arrayAbove tx txLocal outerArray outerCount outerInput outerLength outerValid outerFits outerAbove beforeTx
        (Nat.lt_trans headerBefore array.isLt) branchRun
      refine ⟨middle,run,retained.2,outer.2,retained.1,?_,metadata.1,metadata.2.1,bounded.1,bounded.2.1,transaction_chain_id_normal_index state middle kind typeLocal indexLocal branchRun⟩
      intro name notWord notIndex
      exact transaction_chain_id_other_local state middle name notWord notIndex branchRun

#print axioms transaction_chain_id_returned_heap_outer_contract
end InitECandidate.Runtime
