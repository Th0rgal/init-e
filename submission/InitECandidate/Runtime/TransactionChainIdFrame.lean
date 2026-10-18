import InitECandidate.Runtime.TransactionChainIdFinishFrame
import InitECandidate.Runtime.TxScalarWordLocalCallValue
import InitECandidate.Runtime.TxScalarWordLocalCallFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_chain_id_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (headerBefore : tx.toNat + 8 < array.toNat)
    (run : evaluateHOLFiniteState state transactionChainIdBranch = (none,post)) :
    (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
      RlpSliceInputPrefix post array input inputLength count.toNat := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionChainIdArguments =
      some [.val (.word array),.val (.word (0 : BitVec 64)),.val (.word (8 : BitVec 64)),.val (.word (12 : BitVec 64))] := by
    simp [transactionChainIdArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal]
  unfold transactionChainIdBranch at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      cases run
      exact ⟨fun _ => rfl,valid⟩
    · rw [evaluateHOLFiniteState_seq_line780] at run
      cases callRun : evaluateHOLFiniteState state
          (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionChainIdArguments) with
      | mk result middle =>
        rw [callRun] at run
        cases result with
        | some result => cases run
        | none =>
          dsimp only at run
          have retained := txScalarWord_local_call_normal_frame state middle (ofString "w") _ array 0 8 12 input inputLength scratch frame count ceiling inputLimit
            args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayBelow callRun
          obtain ⟨word,binding⟩ := txScalarWord_local_call_value state middle (ofString "w") _ array 0 8 12 args code callRun
          have txSame : middle.locals.lookup (ofString "tx") = state.locals.lookup (ofString "tx") := by
            apply evaluate_normalLocalFrame (ofString "tx") _ _ state middle callRun
            simp [normalLocalFrameSyntax,show ofString "w" ≠ ofString "tx" by decide]
          have finished := transaction_chain_id_finish_normal_frame middle post tx array count input inputLength word
            (txSame.trans txLocal) binding retained.2 headerBefore (Nat.le_trans arrayBelow (Nat.le_of_lt frame.isLt)) run
          exact ⟨fun watched => (finished.1 watched).trans (retained.1 watched),finished.2.1⟩
  · cases run

#print axioms transaction_chain_id_normal_frame
end InitECandidate.Runtime
