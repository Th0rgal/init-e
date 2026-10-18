import InitECandidate.Runtime.AuthorizationsBodyWholeInputPrefix
import InitECandidate.Runtime.OriginalAuthorizationsCode
import InitECandidate.Runtime.TransactionPairHeaderPrefix
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual authorization decoding and its result stores retain earlier transaction slices. -/
theorem transaction_authorization_decode_normal_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "aul") = some (.rStruct [.val (.word pointer),.val (.word length)]))
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
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (reserve : array.toNat + inputLength.toNat * 248 ≤ frame.toNat)
    (budget : authorizationBodyCost inputLength.toNat + 1 ≤ state.clock)
    (watchedArray watchedCount : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray input inputLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (watchedBeforeArray : watchedArray.toNat + watchedCount.toNat * 16 ≤ array.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (headerBefore : tx.toNat + 280 < watchedArray.toNat)
    (watchedFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64)
    (run : evaluateHOLFiniteState state transactionAuthorizationDecode = (none,final)) :
    RlpSliceInputPrefix final watchedArray input inputLength watchedCount.toNat := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "aul")),.rfield 1 (.var .local (ofString "aul"))] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal]
  have installed : state.code.lookup (ofString "decode_authorizations") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_authorizations,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_authorizations_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_authorizations") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_authorizations) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_transaction_authorization_decode] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "au") (ofString "decode_authorizations") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_decode_authorizations) transactionAuthorizationFinish callee args lookup run
  have entryWatched : RlpSliceInputPrefix entry watchedArray input inputLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := watchedValid slot inside
    exact ⟨p,n,item.after_frame state entry watchedArray slot p n input inputLength rfl rfl rfl⟩
  have bodyWatched := authorization_body_returned_whole_input_prefix entry bodyPost pointer length input inputLength scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound inputBound starts ends wholeBeforeFrame wholeBeforeArray limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayBeforeFrame arrayAligned reserve
    (by change authorizationBodyCost inputLength.toNat ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget)
    watchedArray watchedCount entryWatched watchedBeforeFrame watchedBeforeArray value bodyRun
  obtain ⟨records,count,rfl⟩ := value_two_words_of_checked_shape value checked.1
  let resumed := setVarHOLFinite (ofString "au") (.rStruct [.val (.word records),.val (.word count)]) {bodyPost with locals := state.locals}
  have retained : RlpSliceInputPrefix resumed watchedArray input inputLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := bodyWatched slot inside
    exact ⟨p,n,item.after_frame bodyPost resumed watchedArray slot p n input inputLength rfl rfl rfl⟩
  have atTx : resumed.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "au" ≠ ofString "tx" by decide] using txLocal
  have atResult : resumed.locals.lookup (ofString "au") = some (.rStruct [.val (.word records),.val (.word count)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have stored := transaction_pair_finish_input_prefix resumed (ofString "au") tx records count 272 280 1 watchedArray watchedCount input inputLength
    atTx atResult retained (by change tx.toNat + 272 < watchedArray.toNat; omega)
    (by change tx.toNat + 280 < watchedArray.toNat; exact headerBefore) watchedFits
  rw [← source_transaction_authorization_finish_pair] at stored
  change evaluateHOLFiniteState resumed transactionAuthorizationFinish = (none,output) at tailRun
  rw [tailRun] at stored
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := stored slot inside
  exact ⟨p,n,item.after_frame output _ watchedArray slot p n input inputLength rfl rfl rfl⟩

#print axioms transaction_authorization_decode_normal_prefix
end InitECandidate.Runtime
