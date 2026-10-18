import InitECandidate.Runtime.TransactionToFieldHeapOuterFrame
import InitECandidate.Runtime.TransactionToFieldBound
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_to_returned_heap_outer_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (headerBefore : tx.toNat + 152 < array.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 26) = (some (.returned value),post)) :
    ∃ middle : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle (transactionAt 28) = (some (.returned value),post) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧
      RlpSliceInputPrefix middle outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, middle.globals.lookup watched = state.globals.lookup watched) ∧
      (∀ name, name ≠ ofString "w" → middle.locals.lookup name = state.locals.lookup name) ∧
      middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧
      state.clock ≤ middle.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) ∧
      middle.clock ≤ state.clock := by
  have noReturn := evaluate_noDirectReturn transactionToField (by rfl) state value
  have bounded := evaluate_transaction_to_field_bounded state array index input inputLength scratch frame count.toNat ceiling inputLimit
    arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  have metadata := evaluateHOLFiniteState_metadata state transactionToField
  rw [source_transaction_to,← evaluate_seq_assoc] at run
  change evaluateHOLFiniteState state (.seq transactionToField (transactionAt 28)) = _ at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases fieldRun : evaluateHOLFiniteState state transactionToField with
  | mk result middle =>
    rw [fieldRun] at run noReturn bounded metadata
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      obtain ⟨globals,slices,outer⟩ := transaction_to_field_normal_heap_outer_frame state middle array index
        input inputLength scratch frame count ceiling inputLimit arrayLocal indexLocal valid inside inputBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayFits arrayAbove tx txLocal headerBefore
        outerArray outerCount outerInput outerLength outerValid outerFits outerAbove beforeTx fieldRun
      refine ⟨middle,run,slices,outer,globals,?_,metadata.1,metadata.2.1,bounded.1,bounded.2.1⟩
      intro name notWord
      exact transaction_to_field_other_local state middle name notWord fieldRun

#print axioms transaction_to_returned_heap_outer_contract
end InitECandidate.Runtime
