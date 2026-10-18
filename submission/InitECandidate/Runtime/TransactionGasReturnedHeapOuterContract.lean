import InitECandidate.Runtime.TransactionGasSuffixBound
import InitECandidate.Runtime.TransactionWordFieldHeapOuterFrame
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_gas_returned_heap_outer_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 ≤ state.clock)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (headerBefore : tx.toNat + 144 < array.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 23) = (some (.returned value),post)) :
    ∃ middle : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle (transactionAt 25) = (some (.returned value),post) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧
      RlpSliceInputPrefix middle outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, middle.globals.lookup watched = state.globals.lookup watched) ∧
      (∀ name, name ≠ ofString "w" → middle.locals.lookup name = state.locals.lookup name) ∧
      middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧
      state.clock ≤ middle.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643) ∧
      middle.clock ≤ state.clock := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionGasArguments =
      some [.val (.word array),.val (.word index),.val (.word (0 : BitVec 64)),.val (.word (14 : BitVec 64))] := by
    simp [transactionGasArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have noReturn := evaluate_noDirectReturn (transactionWordField 144 transactionGasArguments) (by rfl) state value
  have bounded := evaluate_transaction_word_field_bounded state (ofString "w")
    (.op .add [.var .local (ofString "tx"),.const 144]) transactionGasArguments array index 0 14 input inputLength scratch frame count.toNat ceiling inputLimit
    args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  change let evaluated := evaluateHOLFiniteState state (transactionWordField 144 transactionGasArguments);
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut at bounded
  have metadata := evaluateHOLFiniteState_metadata state (transactionWordField 144 transactionGasArguments)
  rw [source_transaction_gas_suffix,← evaluate_seq_assoc] at run
  change evaluateHOLFiniteState state (.seq (transactionWordField 144 transactionGasArguments) (transactionAt 25)) = _ at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases fieldRun : evaluateHOLFiniteState state (transactionWordField 144 transactionGasArguments) with
  | mk result middle =>
    rw [fieldRun] at run noReturn bounded metadata
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      obtain ⟨globals,slices,outer⟩ := transaction_word_field_normal_heap_outer_frame state middle array index 0 14
        input inputLength scratch frame count ceiling inputLimit transactionGasArguments args valid inside inputBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayFits arrayAbove tx 144 txLocal headerBefore
        outerArray outerCount outerInput outerLength outerValid outerFits outerAbove beforeTx fieldRun
      refine ⟨middle,run,slices,outer,globals,?_,metadata.1,metadata.2.1,bounded.1,bounded.2.1⟩
      intro name notWord
      apply evaluate_normalLocalFrame name (transactionWordField 144 transactionGasArguments) _ state middle fieldRun
      simp [transactionWordField,normalLocalFrameSyntax,Ne.symm notWord]

#print axioms transaction_gas_returned_heap_outer_contract
end InitECandidate.Runtime
