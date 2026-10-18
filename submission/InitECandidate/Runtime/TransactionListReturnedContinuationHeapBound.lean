import InitECandidate.Runtime.TransactionListReturnedEntryWitness
import InitECandidate.Runtime.TransactionArrayEntryHeapBound
import InitECandidate.Runtime.TransactionRequiredFields
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_list_returned_continuation_heap_bounded {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array input inputLength tx kind expected : BitVec 64) (ceiling inputLimit : Nat)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 ≤ state.clock)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (expectedLocal : state.locals.lookup (ofString "nfields") = some (.val (.word expected)))
    (fields : transactionRequiredFields kind ≤ expected.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (wholeInputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (futureBudget : transactionChainIdSuffixCost inputLength.toNat ≤ post.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state (transactionListCallee pointer length)) (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post)) :
    let resumed := setVarHOLFinite (ofString "lst") value {post with locals := state.locals}
    let evaluated := evaluateHOLFiniteState resumed (transactionAt 13)
    resumed.clock ≤ evaluated.2.clock + transactionChainIdSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut := by
  let resumed := setVarHOLFinite (ofString "lst") value {post with locals := state.locals}
  obtain ⟨count,shape,countBound,valid,heapEqual,growth⟩ := transaction_list_returned_entry_witness state post
    pointer length scratch frame array input inputLength tx kind ceiling inputLimit noWrap lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena heap arrayBound (by omega) heapArena budget inputBeforeFrame inputBeforeArray starts ends
    txLocal typeLocal wholeInputBeforeArray value run
  have listLocal : resumed.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,shape]
  have expectedReady : resumed.locals.lookup (ofString "nfields") = some (.val (.word expected)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "lst" ≠ ofString "nfields" by decide] using expectedLocal
  exact transaction_array_entry_heap_bounded resumed array count expected tx kind input inputLength scratch frame ceiling inputLimit
    valid listLocal expectedReady fields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove wholeInputBeforeFrame headerBefore futureBudget

#print axioms transaction_list_returned_continuation_heap_bounded
end InitECandidate.Runtime
