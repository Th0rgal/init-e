import InitECandidate.Runtime.TransactionNonceSource
import InitECandidate.Runtime.TxScalarWordCallInputBound
import InitECandidate.Runtime.TxScalarU256CallInputBound
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_transaction_nonce_branch_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionNonceBranch
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have wordArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionNonceWordArguments =
      some [.val (.word array),.val (.word index),.val (.word (8 : BitVec 64)),.val (.word (12 : BitVec 64))] := by
    simp [transactionNonceWordArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have wideArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionNonceU256Arguments =
      some [.val (.word array),.val (.word index),.val (.word (32 : BitVec 64))] := by
    simp [transactionNonceU256Arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have word := evaluate_txScalarWord_call_input_bounded state (some (.local,ofString "w")) transactionNonceWordArguments array index 8 12 input inputLength scratch frame filled ceiling inputLimit
    wordArgs valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
  have widened := evaluate_sequence_straight_bounded state
    (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionNonceWordArguments) transactionNonceWiden (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643) word (by rfl)
  have wide := evaluate_txScalarU256_call_input_bounded state (some (.local,ofString "v")) transactionNonceU256Arguments array index 32 input inputLength scratch frame filled ceiling inputLimit
    wideArgs valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  unfold transactionNonceBranch
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact wide
    · dsimp only at widened ⊢
      refine ⟨?_,widened.2.1,widened.2.2⟩
      exact Nat.le_trans widened.1 (Nat.add_le_add_left (by omega) _)
  · dsimp only; exact ⟨by omega,Nat.le_refl _,by simp⟩

#print axioms evaluate_transaction_nonce_branch_bounded
end InitECandidate.Runtime
