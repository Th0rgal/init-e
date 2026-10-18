import InitECandidate.Runtime.TransactionBodyAllocationFailureNoReturn
import InitECandidate.Runtime.TransactionCallBound
import InitECandidate.Runtime.PanLocalCallTerminalHandlerNormal
import InitECandidate.Runtime.PanLocalCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A terminal handler cannot turn an exhausted decoder into a normal call. -/
theorem transaction_handled_call_allocation_failure_terminal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name handlerId handlerVar : MlS) (handler : ProgHOL 64) (arguments : List (ExpHOL 64))
    (input inputLength heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word input),.val (.word inputLength)])
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400)
    (terminal : ∀ current : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState current handler).1 ≠ none)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),some (handlerId,handlerVar,handler)))
      (ofString "decode_transaction_rlp") arguments) = (none,post)) : False := by
  let callee := rlpHeaderCallee input inputLength
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word input)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word inputLength)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "decode_transaction_rlp") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_transaction_rlp,.one) := by
    rw [code]; exact originalRuntimeCode_transactionRlp_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_transaction_rlp") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) .one input inputLength (by decide) installed
  have normal := evaluate_localCall_terminal_handler_normal_result state post name (ofString "decode_transaction_rlp") .one
    arguments _ (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) handler handlerId handlerVar callee args lookup terminal run
  obtain ⟨value,bodyPost,bodyRun,_,_⟩ := evaluate_localCall_normal_result state post name (ofString "decode_transaction_rlp")
    .one arguments _ (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) callee args lookup normal
  have noReturn := transaction_body_allocation_failure_no_return entry input inputLength heap atPointer atLength code heapGlobal request value
  rw [bodyRun] at noReturn
  exact noReturn rfl

#print axioms transaction_handled_call_allocation_failure_terminal
end InitECandidate.Runtime
