import InitECandidate.Runtime.TransactionU256FieldHeapRuntimeFrame
import InitECandidate.Runtime.TransactionFeeLegacyHeapOuterFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem first_budget {cost clock : Nat} (h : 2 * cost ≤ clock) : cost ≤ clock := by omega
private theorem second_budget {cost clock middle : Nat} (h : 2 * cost ≤ clock) (used : clock ≤ middle + cost) : cost ≤ middle := by omega

private theorem sum_consumption {cost before middle after : Nat}
    (first : before ≤ middle + cost) (second : middle ≤ after + cost) : before ≤ after + 2 * cost := by omega

theorem transaction_fee_dynamic_normal_heap_outer_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState state transactionFeeDynamic = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
      RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
      post.locals.lookup (ofString "k") = some (.val (.word (index + 2))) ∧
      state.clock ≤ post.clock + 2 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) (transactionFeeArguments 0) =
      some [.val (.word array),.val (.word index),.val (.word (0 : BitVec 64))] := by
    simp [transactionFeeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  unfold transactionFeeDynamic at run
  rw [← evaluate_seq_assoc,evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : evaluateHOLFiniteState state (.seq (transactionFeeCall 0) (transactionFeeStore 80)) with
  | mk result middle =>
    rw [firstRun] at run
    cases result with
    | some result => cases run
    | none =>
      dsimp only at run
      obtain ⟨slices,outer,globals,locals,postCode,domain,consumed,remaining⟩ :=
        transaction_u256_field_normal_heap_runtime_frame state middle tx 80 (transactionFeeArguments 0)
          array index 0 input inputLength scratch frame count ceiling inputLimit args valid inside inputBound limitBound scratchGlobal frameGlobal
          code orderedFrame framePositive scratchBelow arena (first_budget budget) arrayFits arrayAbove txLocal (by change tx.toNat + 80 + 24 < array.toNat; omega)
          outerArray outerCount outerInput outerLength outerValid outerFits outerAbove beforeTx firstRun
      have atArray := (locals (ofString "arr") (by decide)).trans arrayLocal
      have atIndex := (locals (ofString "k") (by decide)).trans indexLocal
      have atTx := (locals (ofString "tx") (by decide)).trans txLocal
      have nextArgs : evalListHOLFinite middle (h := fun a => Classical.propDecidable (middle.memaddrs a)) (transactionFeeArguments 1) =
          some [.val (.word array),.val (.word (index + 1)),.val (.word (0 : BitVec 64))] := by
        simp [transactionFeeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atArray,atIndex,
          wordOpHOL,wordOp,valueIsWord,valueWord]
      rw [← evaluate_seq_assoc,evaluateHOLFiniteState_seq_line780] at run
      cases secondRun : evaluateHOLFiniteState middle (.seq (transactionFeeCall 1) (transactionFeeStore 112)) with
      | mk result finalState =>
        rw [secondRun] at run
        cases result with
        | some result => cases run
        | none =>
          dsimp only at run
          obtain ⟨finalSlices,finalOuter,finalGlobals,finalLocals,_,_,finalConsumed,_⟩ :=
            transaction_u256_field_normal_heap_runtime_frame middle finalState tx 112 (transactionFeeArguments 1)
              array (index + 1) 0 input inputLength scratch frame count ceiling inputLimit nextArgs slices insideNext inputBound limitBound
              ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal) (postCode.trans code) orderedFrame framePositive scratchBelow
              (by intro address low high; rw [domain]; exact arena address low high) (second_budget budget consumed)
              arrayFits arrayAbove atTx before outerArray outerCount outerInput outerLength outer outerFits outerAbove beforeTx secondRun
          have finalIndex := (finalLocals (ofString "k") (by decide)).trans atIndex
          have advanceRun : evaluateHOLFiniteState finalState (transactionFeeAdvance 2) =
              (none,setVarHOLFinite (ofString "k") (.val (.word (index + 2))) finalState) := by
            apply evaluate_local_word_assignment finalState (ofString "k") _ index (index + 2) finalIndex
            simp [evalHOLExact,evalListHOLExact,finalIndex,wordOpHOL,wordOp,valueIsWord,valueWord]
          rw [advanceRun] at run
          have updated := (Prod.mk.inj run).2.symm
          rw [updated]
          refine ⟨?_,?_,fun watched => (finalGlobals watched).trans (globals watched),?_,sum_consumption consumed finalConsumed⟩
          · intro slot bounded
            obtain ⟨p,n,item⟩ := finalSlices slot bounded
            exact ⟨p,n,RlpSliceInputEntry.after_frame finalState _ _ _ _ _ _ _ item rfl rfl rfl⟩
          · intro slot bounded
            obtain ⟨p,n,item⟩ := finalOuter slot bounded
            exact ⟨p,n,RlpSliceInputEntry.after_frame finalState _ _ _ _ _ _ _ item rfl rfl rfl⟩
          · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms transaction_fee_dynamic_normal_heap_outer_frame
end InitECandidate.Runtime
