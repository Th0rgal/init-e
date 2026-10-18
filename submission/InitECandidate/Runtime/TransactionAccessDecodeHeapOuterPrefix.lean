import InitECandidate.Runtime.AccessListBodyWholeInputHeapOuterPrefix
import InitECandidate.Runtime.OriginalAccessListCode
import InitECandidate.Runtime.TransactionPairHeaderOuterPrefix
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual access decoding and its result stores retain earlier transaction slices. -/
theorem transaction_access_decode_normal_heap_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "al") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (wholeBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (wholeBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (budget : accessBodyCost inputLength.toNat + 1 ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeArray : watchedArray.toNat + watchedCount.toNat * 16 ≤ array.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (headerFits : tx.toNat + 216 < 2^64)
    (run : evaluateHOLFiniteState state transactionAccessDecode = (none,final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "al")),.rfield 1 (.var .local (ofString "al"))] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal]
  have installed : state.code.lookup (ofString "decode_access_list") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_access_list,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_accessList_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_access_list") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_access_list) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_transaction_access_decode] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "acc") (ofString "decode_access_list") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_decode_access_list) transactionAccessFinish callee args lookup run
  have entryWatched : RlpSliceInputPrefix entry watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := watchedValid slot inside
    exact ⟨p,n,item.after_frame state entry watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have bodyWatched := access_body_returned_whole_input_heap_outer_prefix entry bodyPost pointer length input inputLength scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound inputBound starts ends wholeBeforeFrame wholeBeforeArray limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove arrayAligned
    (by change accessBodyCost inputLength.toNat ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget)
    watchedArray watchedCount watchedInput watchedLength entryWatched watchedAbove watchedBeforeArray value bodyRun
  obtain ⟨records,count,rfl⟩ := value_two_words_of_checked_shape value checked.1
  let resumed := setVarHOLFinite (ofString "acc") (.rStruct [.val (.word records),.val (.word count)]) {bodyPost with locals := state.locals}
  have retained : RlpSliceInputPrefix resumed watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := bodyWatched slot inside
    exact ⟨p,n,item.after_frame bodyPost resumed watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have atTx : resumed.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "acc" ≠ ofString "tx" by decide] using txLocal
  have atResult : resumed.locals.lookup (ofString "acc") = some (.rStruct [.val (.word records),.val (.word count)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have stored := transaction_pair_finish_outer_prefix resumed (ofString "acc") tx records count 208 216 1 watchedArray watchedCount watchedInput watchedLength
    atTx atResult retained beforeTx (by change tx.toNat + 208 < 2^64; omega) headerFits
  rw [← source_transaction_access_finish_pair] at stored
  change evaluateHOLFiniteState resumed transactionAccessFinish = (none,output) at tailRun
  rw [tailRun] at stored
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := stored slot inside
  exact ⟨p,n,item.after_frame output _ watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩

#print axioms transaction_access_decode_normal_heap_outer_prefix
end InitECandidate.Runtime
