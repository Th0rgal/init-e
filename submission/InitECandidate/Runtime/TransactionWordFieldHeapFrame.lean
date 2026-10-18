import InitECandidate.Runtime.TransactionWordFieldFrame
import InitECandidate.Runtime.TxScalarWordLocalCallHeapFrame
import InitECandidate.Runtime.TxScalarWordLocalCallValue
import InitECandidate.Runtime.TransactionWordHeaderPrefix
import InitECandidate.Runtime.LocalCallSuccessOtherLocals
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_word_field_normal_heap_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index maximum errorCode input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word maximum),.val (.word errorCode)])
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 ≤ state.clock)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (tx offset : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (headerBefore : tx.toNat + offset.toNat < array.toNat)
    (run : evaluateHOLFiniteState state (transactionWordField offset arguments) = (none,post)) :
    (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
      RlpSliceInputPrefix post array input inputLength count.toNat := by
  unfold transactionWordField at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState state (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") arguments) with
  | mk result middle =>
    rw [callRun] at run
    cases result with
    | some result => cases run
    | none =>
      dsimp only at run
      have kept := txScalarWord_local_call_normal_heap_frame state middle (ofString "w") arguments array index maximum errorCode input inputLength scratch frame count ceiling inputLimit
        args valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayFits arrayAbove callRun
      obtain ⟨word,valueLocal⟩ := txScalarWord_local_call_value state middle (ofString "w") arguments array index maximum errorCode args code callRun
      have same := evaluate_local_call_success_other_locals state (ofString "tx_scalar_word") (ofString "w") arguments (by rw [callRun])
      have txSame := same (ofString "tx") (by decide)
      rw [callRun] at txSame
      have stored := transaction_word_header_prefix middle tx offset array count input inputLength word (ofString "w")
        (txSame.trans txLocal) valueLocal kept.2 headerBefore arrayFits
      rw [run] at stored
      refine ⟨?_,stored⟩
      intro watched
      have globals := evaluate_avoidsGlobalAssignment watched
        (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "w"))) (by rfl) middle
      rw [run] at globals
      exact globals.trans (kept.1 watched)

#print axioms transaction_word_field_normal_heap_frame
end InitECandidate.Runtime
