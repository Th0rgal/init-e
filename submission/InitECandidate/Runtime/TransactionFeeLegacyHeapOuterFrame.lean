import InitECandidate.Runtime.TransactionU256FieldHeapOuterFrame
import InitECandidate.Runtime.TransactionU256FieldBound
import InitECandidate.Runtime.TransactionFeeSource
import InitECandidate.Runtime.TransactionIndexAdvance
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_fee_legacy_normal_heap_outer_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx : BitVec 64)
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
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + 48 + 24 < array.toNat)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state transactionFeeLegacy = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
      RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
      post.locals.lookup (ofString "k") = some (.val (.word (index + 1))) ∧
      state.clock ≤ post.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) (transactionFeeArguments 0) =
      some [.val (.word array),.val (.word index),.val (.word (0 : BitVec 64))] := by
    simp [transactionFeeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  unfold transactionFeeLegacy at run
  rw [← evaluate_seq_assoc,evaluateHOLFiniteState_seq_line780] at run
  cases fieldRun : evaluateHOLFiniteState state (.seq (transactionFeeCall 0) (transactionFeeStore 48)) with
  | mk result middle =>
    rw [fieldRun] at run
    cases result with
    | some result => cases run
    | none =>
      have kept := transaction_u256_field_normal_heap_outer_frame state middle tx 48 (transactionFeeArguments 0)
        array index 0 input inputLength scratch frame count ceiling inputLimit args valid inside inputBound limitBound scratchGlobal frameGlobal
        code orderedFrame framePositive scratchBelow arena budget arrayFits arrayAbove txLocal before
        outerArray outerCount outerInput outerLength outerValid outerFits outerAbove beforeTx fieldRun
      have bounded := evaluate_transaction_u256_field_bounded state (ofString "v")
        (.op .add [.var .local (ofString "tx"),.const 48]) (transactionFeeArguments 0)
        array index 0 input inputLength scratch frame count.toNat ceiling inputLimit args valid inside inputBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
      have literalRun := fieldRun
      unfold transactionFeeCall transactionFeeStore at literalRun
      rw [literalRun] at bounded
      have indexMiddle : middle.locals.lookup (ofString "k") = some (.val (.word index)) :=
        (kept.2.2.2 _ (by decide)).trans indexLocal
      change evaluateHOLFiniteState middle transactionIndexAdvance = (none,post) at run
      rw [transaction_index_advance_run middle index indexMiddle] at run
      have updated := (Prod.mk.inj run).2.symm
      rw [updated]
      refine ⟨?_,?_,kept.2.2.1,?_,bounded.1⟩
      · intro slot bounded
        obtain ⟨p,n,item⟩ := kept.1 slot bounded
        exact ⟨p,n,RlpSliceInputEntry.after_frame middle _ _ _ _ _ _ _ item rfl rfl rfl⟩
      · intro slot bounded
        obtain ⟨p,n,item⟩ := kept.2.1 slot bounded
        exact ⟨p,n,RlpSliceInputEntry.after_frame middle _ _ _ _ _ _ _ item rfl rfl rfl⟩
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms transaction_fee_legacy_normal_heap_outer_frame
end InitECandidate.Runtime
