import InitECandidate.Runtime.TransactionWrapperCallBound
import InitECandidate.Runtime.TransactionWrapperBodyOuterPrefix
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_wrapper_decl_call_outer_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
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
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ tx.toNat)
    (reserve : tx.toNat + 400 + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionWrapperCallCost inputLength.toNat ≤ state.clock)
    (heapSpace : tx.toNat + 400 + inputLength.toNat * 16 ≤ 33806089496)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "decode_transaction") arguments continuation) = (none,post)) :
    ∃ resumed output : PanSemStateFiniteExact 64 F,
      RlpSliceInputPrefix resumed outerArray outerInput outerLength outerCount.toNat ∧
      evaluateHOLFiniteState resumed continuation = (none,output) ∧ post.memory = output.memory := by
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
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state post name (ofString "decode_transaction")
    .one .one arguments _ (sourceFunctionBody Guest.guestFn_decode_transaction) continuation callee args lookup run
  have entryOuter : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := outerValid slot within
    exact ⟨p,n,item.after_frame state entry outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have ticks : transactionCallCost inputLength.toNat ≤ entry.clock := by
    change _ ≤ state.clock - 1
    have available : 1 + transactionCallCost inputLength.toNat ≤ state.clock := budget
    omega
  have retained := transaction_wrapper_body_returned_outer_prefix entry bodyPost input inputLength scratch frame tx ceiling inputLimit
    atPointer atLength noWrap inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap txBound countLimit heapArena inputBeforeFrame inputBeforeArray reserve txAligned ticks heapSpace
    outerArray outerCount outerInput outerLength entryOuter outerBelow beforeTx value bodyRun
  let resumed := setVarHOLFinite name value {bodyPost with locals := state.locals}
  refine ⟨resumed,output,?_,tailRun,?_⟩
  · intro slot within
    obtain ⟨p,n,item⟩ := retained slot within
    exact ⟨p,n,item.after_frame bodyPost resumed outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  · rw [restored]

#print axioms transaction_wrapper_decl_call_outer_contract
end InitECandidate.Runtime
