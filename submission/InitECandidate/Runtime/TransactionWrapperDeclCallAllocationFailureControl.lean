import InitECandidate.Runtime.PanDecCallNonreturningBody
import InitECandidate.Runtime.TransactionWrapperBodyAllocationFailureNoReturn
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.TransactionWrapperBodyAllocationFailureBound
import InitECandidate.Runtime.TransactionWrapperCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual decoder calls with an exhausted initial heap terminate within
four source ticks, without input-span or successful-allocation reserves. -/
theorem transaction_wrapper_decl_call_allocation_failure_control {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (input inputLength heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word input),.val (.word inputLength)])
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) :
    (evaluateHOLFiniteState state (.decCall name shape (ofString "decode_transaction") arguments continuation)).1 ≠ none ∧
    (∀ value, (evaluateHOLFiniteState state (.decCall name shape (ofString "decode_transaction") arguments continuation)).1 ≠ some (.returned value)) := by
  let callee := rlpHeaderCallee input inputLength
  let entry := callEntryStateHOLFinite state callee
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word inputLength)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word input)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have installed : state.code.lookup (ofString "decode_transaction") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_transaction,.one) := by
    rw [code]; exact originalRuntimeCode_transactionWrapper_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_transaction") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_transaction) .one input inputLength (by decide) installed
  apply evaluate_decCall_nonreturning_body_control state name (ofString "decode_transaction") shape .one arguments
    [.val (.word input),.val (.word inputLength)] (sourceFunctionBody Guest.guestFn_decode_transaction) continuation callee args lookup
  intro value equal
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_transaction) with
  | mk result post =>
    rw [bodyRun] at equal
    dsimp only at equal
    subst result
    exact transaction_wrapper_body_allocation_failure_no_return entry post input inputLength heap atPointer atLength code heapGlobal request value bodyRun

#print axioms transaction_wrapper_decl_call_allocation_failure_control
end InitECandidate.Runtime
