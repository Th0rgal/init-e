import InitECandidate.Runtime.TransactionWrapperCallGuardedHeapBound
import InitECandidate.Runtime.OriginalTransactionWrapperCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.VersionedHashesTypedScanCallBound
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.PanEvaluationMetadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString



theorem evaluate_versioned_hashes_transaction_step_guarded_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ tx.toNat)
    (heapAbove : ceiling ≤ tx.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionWrapperCallCost inputLength.toNat + (1 + versionedHashesScanCost) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall (ofString "tx") .one (ofString "decode_transaction") arguments
      (.decCall (ofString "isb") .one (ofString "tx_is_blob") [.var .local (ofString "tx")] versionedHashesScanTail))
    state.clock ≤ evaluated.2.clock + (transactionWrapperCallCost inputLength.toNat + (1 + versionedHashesScanCost)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := rlpHeaderCallee input inputLength
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word input)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word inputLength)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ticks : 1 + transactionCallCost inputLength.toNat ≤ state.clock := by
    change 1 + transactionCallCost inputLength.toNat + (1 + versionedHashesScanCost) ≤ state.clock at budget
    omega
  have bounded := evaluate_transaction_wrapper_body_guarded_heap_bounded entry input inputLength scratch frame tx ceiling inputLimit
    atPointer atLength noWrap inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap heapWithin countLimit heapArena inputBeforeFrame inputBeforeArray heapAbove txAligned
    (by change _ ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "decode_transaction") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_transaction,.one) := by
    rw [code]; exact originalRuntimeCode_transactionWrapper_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_transaction") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_transaction) .one input inputLength (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_transaction) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have entryClock : entry.clock = state.clock - 1 := rfl
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_transaction)
    rw [bodyRun] at metadata
    apply evaluate_decCall_checked_continuation_bounded state post (ofString "tx") (ofString "decode_transaction") .one .one
      arguments [.val (.word input),.val (.word inputLength)] (sourceFunctionBody Guest.guestFn_decode_transaction)
      (.decCall (ofString "isb") .one (ofString "tx_is_blob") [.var .local (ofString "tx")] versionedHashesScanTail)
      callee result (transactionWrapperCallCost inputLength.toNat) (1 + versionedHashesScanCost)
      args lookup (by omega) bodyRun bounded.2.1
      (by change state.clock ≤ post.clock + (1 + transactionCallCost inputLength.toNat); omega) bounded.2.2
    intro value returned checked
    cases value with
    | rStruct fields => simp [shapeOfHOLExact,shapeEqHOL] at checked
    | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL] at checked
    | val atom =>
      cases atom with
      | word pointer =>
        let resumed := setVarHOLFinite (ofString "tx") (.val (.word pointer)) {post with locals := state.locals}
        have pointerLocal : resumed.locals.lookup (ofString "tx") = some (.val (.word pointer)) := by
          simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        have vhResumed : resumed.locals.lookup (ofString "vh") = some (.val (.word vh)) := by
          simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
            show ofString "tx" ≠ ofString "vh" by decide] using vhLocal
        have cursorResumed : resumed.locals.lookup (ofString "k") = some (.val (.word cursor)) := by
          simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
            show ofString "tx" ≠ ofString "k" by decide] using cursorLocal
        exact evaluate_versioned_hashes_typed_scan_bounded resumed pointer vh cursor pointerLocal vhResumed cursorResumed
          (metadata.1.trans code) (by
            change 1 + versionedHashesScanCost ≤ post.clock
            have cost := bounded.1
            change state.clock - 1 ≤ post.clock + transactionCallCost inputLength.toNat at cost
            change 1 + transactionCallCost inputLength.toNat + (1 + versionedHashesScanCost) ≤ state.clock at budget
            omega)

#print axioms evaluate_versioned_hashes_transaction_step_guarded_heap_bounded
end InitECandidate.Runtime
