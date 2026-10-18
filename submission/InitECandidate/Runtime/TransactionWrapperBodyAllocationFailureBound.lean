import InitECandidate.Runtime.TransactionWrapperBodyBound
import InitECandidate.Runtime.TransactionHandledCallAllocationFailureBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete wrapper preserves the exhausted-heap decoder bound through
its local declarations, terminal exception translation, and final return. -/
theorem evaluate_transaction_wrapper_body_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (input inputLength heap : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 3 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction)
    state.clock ≤ evaluated.2.clock + 3 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "tx") (.val (.word 0)) state
  let ready := setVarHOLFinite (ofString "rc") (.val (.word 0)) entered
  have locals : ∀ key, key ≠ ofString "tx" → key ≠ ofString "rc" → ready.locals.lookup key = state.locals.lookup key := by
    intro key notTx notRc
    simp [ready,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notTx,Ne.symm notRc]
  have args : evalListHOLFinite ready (h := fun address => Classical.propDecidable (ready.memaddrs address)) transactionWrapperArguments =
      some [.val (.word input),.val (.word inputLength)] := by
    simp [transactionWrapperArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      (locals _ (by decide) (by decide)).trans pointerLocal,(locals _ (by decide) (by decide)).trans lengthLocal]
  have bounded := evaluate_transaction_handled_call_allocation_failure_bounded ready (some (.local,ofString "tx")) transactionWrapperArguments
    (ofString "RlpErr") (ofString "rc") transactionWrapperHandler transaction_wrapper_handler_straight
    input inputLength heap args code heapGlobal request budget
  change ready.clock ≤ (evaluateHOLFiniteState ready transactionWrapperCall).2.clock + 3 ∧
    (evaluateHOLFiniteState ready transactionWrapperCall).2.clock ≤ ready.clock ∧
    (evaluateHOLFiniteState ready transactionWrapperCall).1 ≠ some .timeOut at bounded
  have combined := evaluate_sequence_straight_bounded ready transactionWrapperCall (.return (.var .local (ofString "tx")))
    3 bounded (by rfl)
  have initial (current : PanSemStateFiniteExact 64 F) : @evalHOLExact 64 F _ current.toExact
      (fun address => Classical.propDecidable (current.memaddrs address)) (.const 0) = some (.val (.word (0 : BitVec 64))) := rfl
  have checked : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  rw [source_transaction_wrapper,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial state]
  dsimp only
  rw [checked]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial entered]
  dsimp only
  rw [checked]
  exact combined


#print axioms evaluate_transaction_wrapper_body_allocation_failure_bounded
end InitECandidate.Runtime
