import InitECandidate.Runtime.TransactionNonceWidenValue
import InitECandidate.Runtime.TxScalarWordLocalCallValue
import InitECandidate.Runtime.TxScalarWordLocalCallFrame
import InitECandidate.Runtime.TxScalarU256LocalCallOuterPrefix
import InitECandidate.Runtime.TxScalarWordLocalCallOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_nonce_branch_normal_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (run : evaluateHOLFiniteState state transactionNonceBranch = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  have wordArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionNonceWordArguments =
      some [.val (.word array),.val (.word index),.val (.word (8 : BitVec 64)),.val (.word (12 : BitVec 64))] := by
    simp [transactionNonceWordArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have wideArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionNonceU256Arguments =
      some [.val (.word array),.val (.word index),.val (.word (32 : BitVec 64))] := by
    simp [transactionNonceU256Arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  unfold transactionNonceBranch at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · exact txScalarU256_local_call_outer_prefix state post (ofString "v") _ array index 32 input inputLength scratch frame count ceiling inputLimit
        wideArgs valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget outerArray outerCount outerInput outerLength outerValid outerBelow run
    · rw [evaluateHOLFiniteState_seq_line780] at run
      cases callRun : evaluateHOLFiniteState state
          (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionNonceWordArguments) with
      | mk result middle =>
        rw [callRun] at run
        cases result with
        | some result => cases run
        | none =>
          dsimp only at run
          have retained := txScalarWord_local_call_outer_prefix state middle (ofString "w") _ array index 8 12 input inputLength scratch frame count ceiling inputLimit
            wordArgs valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega) outerArray outerCount outerInput outerLength outerValid outerBelow callRun
          obtain ⟨word,binding⟩ := txScalarWord_local_call_value state middle (ofString "w") _ array index 8 12 wordArgs code callRun
          rw [transaction_nonce_widen_normal middle post word binding run]
          intro slot bounded
          obtain ⟨p,n,item⟩ := retained slot bounded
          exact ⟨p,n,item.after_frame middle _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  · cases run

#print axioms transaction_nonce_branch_normal_outer_prefix
end InitECandidate.Runtime
