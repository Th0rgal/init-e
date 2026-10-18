import InitECandidate.Runtime.TwoWordValueShape
import InitECandidate.Runtime.VersionedHashesTypedScanReadFrame
import InitECandidate.Runtime.TransactionWrapperCallBound
import InitECandidate.Runtime.TransactionWrapperBodyGuardedHeapOuterPrefix
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem versioned_hashes_transaction_step_normal_guarded_heap_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (vh cursor : BitVec 64)
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
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
    (heapWithin : tx.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ tx.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionWrapperCallCost inputLength.toNat ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state (.decCall (ofString "tx") .one (ofString "decode_transaction") arguments (.decCall (ofString "isb") .one (ofString "tx_is_blob") [.var .local (ofString "tx")] versionedHashesScanTail)) = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
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
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state post (ofString "tx") (ofString "decode_transaction")
    .one .one arguments _ (sourceFunctionBody Guest.guestFn_decode_transaction)
    (.decCall (ofString "isb") .one (ofString "tx_is_blob") [.var .local (ofString "tx")] versionedHashesScanTail) callee args lookup run
  have entryOuter : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := outerValid slot within
    exact ⟨p,n,item.after_frame state entry outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have ticks : transactionCallCost inputLength.toNat ≤ entry.clock := by
    change _ ≤ state.clock - 1
    have available : 1 + transactionCallCost inputLength.toNat ≤ state.clock := budget
    omega
  have retained := transaction_wrapper_body_returned_guarded_heap_outer_prefix entry bodyPost input inputLength scratch frame tx ceiling inputLimit
    atPointer atLength noWrap inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap heapWithin countLimit heapArena inputBeforeFrame inputBeforeArray txAligned ticks
    outerArray outerCount outerInput outerLength entryOuter outerAbove beforeTx value bodyRun
  obtain ⟨pointer,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked.1)
  let resumed := setVarHOLFinite (ofString "tx") (.val (.word pointer)) {bodyPost with locals := state.locals}
  have atTx : resumed.locals.lookup (ofString "tx") = some (.val (.word pointer)) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atVh : resumed.locals.lookup (ofString "vh") = some (.val (.word vh)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "tx" ≠ ofString "vh" by decide] using vhLocal
  have atK : resumed.locals.lookup (ofString "k") = some (.val (.word cursor)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "tx" ≠ ofString "k" by decide] using cursorLocal
  have bodyMetadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_transaction)
  rw [bodyRun] at bodyMetadata
  have readFrame := versioned_hashes_typed_scan_normal_read_frame resumed output pointer vh cursor atTx atVh atK
    (bodyMetadata.1.trans code) tailRun
  have metadata := evaluateHOLFiniteState_metadata resumed
    (.decCall (ofString "isb") .one (ofString "tx_is_blob") [.var .local (ofString "tx")] versionedHashesScanTail)
  rw [tailRun] at metadata
  rw [restored]
  intro slot within
  obtain ⟨p,n,item⟩ := retained slot within
  exact ⟨p,n,item.after_frame bodyPost _ outerArray slot p n outerInput outerLength metadata.2.1
    (congrFun readFrame.1 _) (congrFun readFrame.1 _)⟩

#print axioms versioned_hashes_transaction_step_normal_guarded_heap_outer_prefix
end InitECandidate.Runtime
