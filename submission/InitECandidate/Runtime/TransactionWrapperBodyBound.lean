import InitECandidate.Runtime.TransactionWrapperSource
import InitECandidate.Runtime.PanSeqStraightBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_transaction_wrapper_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (input inputLength scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (noWrap : input.toNat + inputLength.toNat < 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (txBound : tx.toNat + 400 ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ tx.toNat)
    (reserve : tx.toNat + 400 + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionCallCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction)
    state.clock ≤ evaluated.2.clock + transactionCallCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "tx") (.val (.word 0)) state
  let ready := setVarHOLFinite (ofString "rc") (.val (.word 0)) entered
  have locals : ∀ key, key ≠ ofString "tx" → key ≠ ofString "rc" → ready.locals.lookup key = state.locals.lookup key := by
    intro key notTx notRc
    simp [ready,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notTx,Ne.symm notRc]
  have args : evalListHOLFinite ready (h := fun address => Classical.propDecidable (ready.memaddrs address)) transactionWrapperArguments =
      some [.val (.word input),.val (.word inputLength)] := by
    simp [transactionWrapperArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      (locals _ (by decide) (by decide)).trans pointerLocal,(locals _ (by decide) (by decide)).trans lengthLocal]
  have bounded := evaluate_transaction_handled_call_bounded ready (some (.local,ofString "tx")) transactionWrapperArguments
    (ofString "RlpErr") (ofString "rc") transactionWrapperHandler transaction_wrapper_handler_straight
    input inputLength scratch frame tx ceiling inputLimit args noWrap inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena heap txBound countLimit heapArena inputBeforeFrame inputBeforeArray reserve txAligned budget
  change ready.clock ≤ (evaluateHOLFiniteState ready transactionWrapperCall).2.clock + transactionCallCost inputLength.toNat ∧
    (evaluateHOLFiniteState ready transactionWrapperCall).2.clock ≤ ready.clock ∧
    (evaluateHOLFiniteState ready transactionWrapperCall).1 ≠ some .timeOut at bounded
  have combined := evaluate_sequence_straight_bounded ready transactionWrapperCall (.return (.var .local (ofString "tx")))
    (transactionCallCost inputLength.toNat) bounded (by rfl)
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

#print axioms evaluate_transaction_wrapper_body_bounded
end InitECandidate.Runtime
