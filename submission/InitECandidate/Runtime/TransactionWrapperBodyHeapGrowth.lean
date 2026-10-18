import InitECandidate.Runtime.TransactionWrapperBodyBound
import InitECandidate.Runtime.TransactionTerminalHandlerCallHeapGrowth
import InitECandidate.Runtime.PanLocalCallHandlerNoReturn
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.ReadOnlyMemory
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_wrapper_body_returned_heap_growth {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : transactionCallCost inputLength.toNat ≤ state.clock)
    (heapSpace : tx.toNat + 400 + inputLength.toNat * 16 ≤ 33806089496)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction) = (some (.returned value),post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      tx.toNat ≤ nextHeap.toNat ∧
      nextHeap.toNat ≤ tx.toNat + 400 + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 280 ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
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
    | some result => exact False.elim (noReturn (Prod.mk.inj bodyRun).1)
    | none =>
      have readyOuter : RlpSliceInputPrefix ready outerArray outerInput outerLength outerCount.toNat := by
        intro slot within
        obtain ⟨p,n,item⟩ := outerValid slot within
        exact ⟨p,n,item.after_frame state ready outerArray slot p n outerInput outerLength rfl rfl rfl⟩
      obtain ⟨nextHeap,binding,lower,upper,heapBound,heapAligned,scratchFinal,frameFinal⟩ := transaction_terminal_handler_call_heap_growth ready middle (ofString "tx") transactionWrapperArguments
        input inputLength scratch frame tx ceiling inputLimit args noWrap inputBound limitBound scratchGlobal frameGlobal code
        orderedFrame framePositive scratchBelow arena heap txBound countLimit heapArena inputBeforeFrame inputBeforeArray reserve txAligned budget
        heapSpace outerArray outerCount outerInput outerLength readyOuter outerBelow beforeTx callRun
      have globals := evaluate_avoidsGlobalAssignment (ofString "heap_ptr") (.return (.var .local (ofString "tx"))) (by rfl) middle
      have scratchGlobals := evaluate_avoidsGlobalAssignment (ofString "scratch_ptr") (.return (.var .local (ofString "tx"))) (by rfl) middle
      have frameGlobals := evaluate_avoidsGlobalAssignment (ofString "frame_mem_ptr") (.return (.var .local (ofString "tx"))) (by rfl) middle
      dsimp only at bodyRun
      rw [bodyRun] at globals scratchGlobals frameGlobals
      rw [outerRestore,innerRestore]
      exact ⟨nextHeap,globals.trans binding,lower,upper,heapBound,heapAligned,
        scratchGlobals.trans scratchFinal,frameGlobals.trans frameFinal⟩

#print axioms transaction_wrapper_body_returned_heap_growth
end InitECandidate.Runtime
