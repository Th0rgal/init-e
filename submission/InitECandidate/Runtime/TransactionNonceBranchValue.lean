import InitECandidate.Runtime.TransactionNonceWidenValue
import InitECandidate.Runtime.TxScalarWordLocalCallValue
import InitECandidate.Runtime.TxScalarU256LocalCallValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both original nonce decoding paths produce four word limbs. -/
theorem transaction_nonce_branch_four_words {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state transactionNonceBranch = (none,post)) :
    ∃ first second third fourth : BitVec 64,
      post.locals.lookup (ofString "v") =
        some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) := by
  have wordArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      transactionNonceWordArguments =
      some [.val (.word array),.val (.word index),.val (.word (8 : BitVec 64)),.val (.word (12 : BitVec 64))] := by
    simp [transactionNonceWordArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have u256Args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      transactionNonceU256Arguments =
      some [.val (.word array),.val (.word index),.val (.word (32 : BitVec 64))] := by
    simp [transactionNonceU256Arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  unfold transactionNonceBranch at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · exact txScalarU256_local_call_value state post (ofString "v") _ array index 32 u256Args code run
    · rw [evaluateHOLFiniteState_seq_line780] at run
      cases callRun : evaluateHOLFiniteState state
          (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionNonceWordArguments) with
      | mk result middle =>
        rw [callRun] at run
        cases result with
        | some result => cases run
        | none =>
          dsimp only at run
          obtain ⟨word,binding⟩ := txScalarWord_local_call_value state middle (ofString "w") _ array index 8 12 wordArgs code callRun
          exact ⟨word,0,0,0,(transaction_nonce_widen_value_frame middle post word binding run).1⟩
  · cases run

#print axioms transaction_nonce_branch_four_words
end InitECandidate.Runtime
