import InitECandidate.Runtime.TransactionChainIdSource
import InitECandidate.Runtime.TxScalarWordCallInputBound
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_transaction_chain_id_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : 0 < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionChainIdBranch
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionChainIdArguments =
      some [.val (.word array),.val (.word (0 : BitVec 64)),.val (.word (8 : BitVec 64)),.val (.word (12 : BitVec 64))] := by
    simp [transactionChainIdArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal]
  have word := evaluate_txScalarWord_call_input_bounded state (some (.local,ofString "w")) transactionChainIdArguments array 0 8 12 input inputLength scratch frame filled ceiling inputLimit
    args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  have finished := evaluate_sequence_straight_bounded state
    (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionChainIdArguments) transactionChainIdFinish
    (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643) word (by rfl)
  unfold transactionChainIdBranch
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]; dsimp only
      exact ⟨by omega,Nat.le_refl _,by simp⟩
    · exact finished
  · dsimp only; exact ⟨by omega,Nat.le_refl _,by simp⟩

#print axioms evaluate_transaction_chain_id_bounded
end InitECandidate.Runtime
