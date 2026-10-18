import InitECandidate.Runtime.TransactionWrapperCallBound
import InitECandidate.Runtime.TransactionWrapperBodyHeapGrowth
import InitECandidate.Runtime.PanLocalCallNormalResult
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_wrapper_local_call_heap_growth {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64))
    (input inputLength scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word input),.val (.word inputLength)])
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
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ tx.toNat)
    (reserve : tx.toNat + 400 + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionWrapperCallCost inputLength.toNat ≤ state.clock)
    (heapSpace : tx.toNat + 400 + inputLength.toNat * 16 ≤ 33806089496)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "decode_transaction") arguments) = (none,post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      tx.toNat ≤ nextHeap.toNat ∧
      nextHeap.toNat ≤ tx.toNat + 400 + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 280 ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  let callee := rlpHeaderCallee input inputLength
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word input)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word inputLength)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "decode_transaction") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_transaction,.one) := by
    rw [code]; exact originalRuntimeCode_transactionWrapper_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_transaction") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_transaction) .one input inputLength (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name (ofString "decode_transaction")
    .one arguments _ (sourceFunctionBody Guest.guestFn_decode_transaction) callee args lookup run
  have entryOuter : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := outerValid slot within
    exact ⟨p,n,item.after_frame state entry outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have ticks : transactionCallCost inputLength.toNat ≤ entry.clock := by
    change _ ≤ state.clock - 1
    have available : 1 + transactionCallCost inputLength.toNat ≤ state.clock := budget
    omega
  obtain ⟨nextHeap,binding,lower,upper,heapBound,heapAligned,scratchFinal,frameFinal⟩ := transaction_wrapper_body_returned_heap_growth entry bodyPost input inputLength scratch frame tx ceiling inputLimit
    atPointer atLength noWrap inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap txBound countLimit heapArena inputBeforeFrame inputBeforeArray reserve txAligned ticks heapSpace
    outerArray outerCount outerInput outerLength entryOuter outerBelow beforeTx value bodyRun
  rw [restored]
  exact ⟨nextHeap,binding,lower,upper,heapBound,heapAligned,scratchFinal,frameFinal⟩

#print axioms transaction_wrapper_local_call_heap_growth
end InitECandidate.Runtime
