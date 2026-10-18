import InitECandidate.Runtime.TransactionWrapperBodyAllocationFailureNoReturn
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.TransactionWrapperBodyAllocationFailureBound
import InitECandidate.Runtime.TransactionWrapperCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual decoder calls with an exhausted initial heap terminate within
four source ticks, without input-span or successful-allocation reserves. -/
theorem evaluate_transaction_wrapper_decl_call_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (input inputLength heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word input),.val (.word inputLength)])
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 4 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape (ofString "decode_transaction") arguments continuation)
    state.clock ≤ evaluated.2.clock + 4 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := rlpHeaderCallee input inputLength
  let entry := callEntryStateHOLFinite state callee
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word inputLength)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word input)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have bounded := evaluate_transaction_wrapper_body_allocation_failure_bounded entry input inputLength heap atPointer atLength code heapGlobal request
    (by change 3 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "decode_transaction") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_transaction,.one) := by
    rw [code]; exact originalRuntimeCode_transactionWrapper_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_transaction") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_transaction) .one input inputLength (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_transaction) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    apply evaluate_decCall_checked_continuation_bounded state post name (ofString "decode_transaction") shape .one arguments
      [.val (.word input),.val (.word inputLength)] (sourceFunctionBody Guest.guestFn_decode_transaction) continuation callee
      result 4 0 args lookup (by omega) bodyRun bounded.2.1
      (by have spent := bounded.1; change state.clock - 1 ≤ post.clock + 3 at spent; omega) bounded.2.2
    intro value returned checked
    exact False.elim (transaction_wrapper_body_allocation_failure_no_return entry post input inputLength heap
      atPointer atLength code heapGlobal request value (by rw [bodyRun,returned]))

#print axioms evaluate_transaction_wrapper_decl_call_allocation_failure_bounded
end InitECandidate.Runtime
