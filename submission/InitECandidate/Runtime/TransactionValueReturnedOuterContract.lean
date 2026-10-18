import InitECandidate.Runtime.TransactionValueSuffixBound
import InitECandidate.Runtime.TransactionU256FieldOuterFrame
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_value_returned_outer_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (headerBefore : tx.toNat + 160 + 24 < array.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 29) = (some (.returned value),post)) :
    ∃ middle : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle (transactionAt 31) = (some (.returned value),post) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧
      RlpSliceInputPrefix middle outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, middle.globals.lookup watched = state.globals.lookup watched) ∧
      (∀ name, name ≠ ofString "v" → middle.locals.lookup name = state.locals.lookup name) ∧
      middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧
      state.clock ≤ middle.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      middle.clock ≤ state.clock := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionValueArguments =
      some [.val (.word array),.val (.word index),.val (.word (32 : BitVec 64))] := by
    simp [transactionValueArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have noReturn := evaluate_noDirectReturn (transactionU256Field 160 transactionValueArguments) (by rfl) state value
  have bounded := evaluate_transaction_u256_field_bounded state (ofString "v")
    (.op .add [.var .local (ofString "tx"),.const 160]) transactionValueArguments array index 32 input inputLength scratch frame count.toNat ceiling inputLimit
    args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  change let evaluated := evaluateHOLFiniteState state (transactionU256Field 160 transactionValueArguments);
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut at bounded
  have metadata := evaluateHOLFiniteState_metadata state (transactionU256Field 160 transactionValueArguments)
  rw [source_transaction_value_suffix,← evaluate_seq_assoc] at run
  change evaluateHOLFiniteState state (.seq (transactionU256Field 160 transactionValueArguments) (transactionAt 31)) = _ at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases fieldRun : evaluateHOLFiniteState state (transactionU256Field 160 transactionValueArguments) with
  | mk result middle =>
    rw [fieldRun] at run noReturn bounded metadata
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      obtain ⟨slices,outer,globals,otherLocals⟩ := transaction_u256_field_normal_outer_frame state middle tx 160 transactionValueArguments
        array index 32 input inputLength scratch frame count ceiling inputLimit args valid inside inputBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayBelow txLocal headerBefore
        outerArray outerCount outerInput outerLength outerValid outerBelow beforeTx fieldRun
      refine ⟨middle,run,slices,outer,globals,?_,metadata.1,metadata.2.1,bounded.1,bounded.2.1⟩
      intro name notWord
      exact otherLocals name notWord

#print axioms transaction_value_returned_outer_contract
end InitECandidate.Runtime
