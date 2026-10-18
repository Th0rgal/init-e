import InitECandidate.Runtime.TransactionWrapperBodyOuterPrefix
import InitECandidate.Runtime.TransactionHandledCallAllocationFailureTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Initial heap exhaustion propagates through the complete wrapper: its
exception translation cannot manufacture a successful transaction pointer. -/
theorem transaction_wrapper_body_allocation_failure_no_return {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (input inputLength heap : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction) = (some (.returned value),post)) : False := by
  let entered := setVarHOLFinite (ofString "tx") (.val (.word 0)) state
  let ready := setVarHOLFinite (ofString "rc") (.val (.word 0)) entered
  have locals : ∀ key, key ≠ ofString "tx" → key ≠ ofString "rc" → ready.locals.lookup key = state.locals.lookup key := by
    intro key notTx notRc
    simp [ready,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notTx,Ne.symm notRc]
  have args : evalListHOLFinite ready (h := fun address => Classical.propDecidable (ready.memaddrs address)) transactionWrapperArguments =
      some [.val (.word input),.val (.word inputLength)] := by
    simp [transactionWrapperArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      (locals _ (by decide) (by decide)).trans pointerLocal,(locals _ (by decide) (by decide)).trans lengthLocal]
  rw [source_transaction_wrapper] at run
  obtain ⟨outerOutput,outerRun,outerRestore⟩ := evaluate_dec_word_result_scope state post (ofString "tx") (.const 0) 0 _ _ rfl run
  obtain ⟨output,bodyRun,innerRestore⟩ := evaluate_dec_word_result_scope entered outerOutput (ofString "rc") (.const 0) 0 _ _ rfl outerRun
  have installed : ready.code.lookup (ofString "decode_transaction_rlp") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_transaction_rlp,.one) := by
    change state.code.lookup _ = _
    rw [code]; exact originalRuntimeCode_transactionRlp_lookup
  have lookup := pan_two_word_lookup_shape ready.code.lookup (ofString "decode_transaction_rlp") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) .one input inputLength (by decide) installed
  have noReturn : (evaluateHOLFiniteState ready transactionWrapperCall).1 ≠ some (.returned value) := by
    intro equal
    cases callRun : evaluateHOLFiniteState ready transactionWrapperCall with
    | mk result middle =>
      rw [callRun] at equal
      dsimp only at equal
      subst result
      exact evaluate_localCall_handler_no_return ready middle (ofString "tx") (ofString "decode_transaction_rlp") .one
        transactionWrapperArguments _ (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) transactionWrapperHandler
        (ofString "RlpErr") (ofString "rc") (rlpHeaderCallee input inputLength) args lookup value
        (by intro current; exact evaluate_noDirectReturn transactionWrapperHandler (by rfl) current value) callRun
  rw [evaluateHOLFiniteState_seq_line780] at bodyRun
  cases callRun : evaluateHOLFiniteState ready transactionWrapperCall with
  | mk result middle =>
    rw [callRun] at bodyRun noReturn
    cases result with
    | some result => exact noReturn (Prod.mk.inj bodyRun).1
    | none =>
      exact transaction_handled_call_allocation_failure_terminal ready middle (ofString "tx") (ofString "RlpErr") (ofString "rc")
        transactionWrapperHandler transactionWrapperArguments input inputLength heap args code heapGlobal request
        (by intro current; exact evaluate_raise_terminal current (ofString "TxErr") (.op .add [.const 100,.var .local (ofString "rc")])) callRun

#print axioms transaction_wrapper_body_allocation_failure_no_return
end InitECandidate.Runtime
