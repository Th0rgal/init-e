import InitECandidate.Runtime.CallStraightHandlerClockNoTimeout
import InitECandidate.Runtime.TransactionBodyAllocationFailureBound
import InitECandidate.Runtime.TransactionCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual decoder calls with an exhausted initial heap terminate within
three source ticks, without input-span or successful-allocation reserves. -/
theorem evaluate_transaction_handled_call_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (handlerId handlerVar : MlS) (handlerProgram : ProgHOL 64) (supported : straightLine handlerProgram = true)
    (input inputLength heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word input),.val (.word inputLength)])
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 3 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,some (handlerId,handlerVar,handlerProgram))) (ofString "decode_transaction_rlp") arguments)
    state.clock ≤ evaluated.2.clock + 3 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := rlpHeaderCallee input inputLength
  let entry := callEntryStateHOLFinite state callee
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word inputLength)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := transaction_body_allocation_failure_bounded entry inputLength heap atLength code heapGlobal request
    (by change 2 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "decode_transaction_rlp") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_transaction_rlp,.one) := by
    rw [code]; exact originalRuntimeCode_transactionRlp_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_transaction_rlp") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) .one input inputLength (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have output := evaluate_call_straight_handler_clock_no_timeout state post (ofString "decode_transaction_rlp") destination
      handlerId handlerVar handlerProgram supported arguments _
      (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) callee .one result args lookup (by omega) bodyRun bounded.2.2
    dsimp only
    rw [output.2]
    refine ⟨?_,?_,output.1⟩
    · have spent := bounded.1
      change state.clock - 1 ≤ post.clock + 2 at spent
      change state.clock ≤ post.clock + 3
      omega
    · have remaining := bounded.2.1
      change post.clock ≤ state.clock - 1 at remaining
      change post.clock ≤ state.clock
      omega

#print axioms evaluate_transaction_handled_call_allocation_failure_bounded
end InitECandidate.Runtime
