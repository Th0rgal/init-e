import InitECandidate.Runtime.BlobHashesBodyWholeInputOuterPrefix
import InitECandidate.Runtime.OriginalBlobHashesCode
import InitECandidate.Runtime.TransactionPairHeaderOuterPrefix
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual blob decoding and its result stores retain earlier transaction slices. -/
theorem transaction_blob_decode_normal_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "bl") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (budget : blobHashesBodyCost inputLength.toNat + 1 ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (watchedBeforeArray : watchedArray.toNat + watchedCount.toNat * 16 ≤ array.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (headerFits : tx.toNat + 264 < 2^64)
    (run : evaluateHOLFiniteState state transactionBlobDecode = (none,final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "bl")),.rfield 1 (.var .local (ofString "bl"))] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal]
  have installed : state.code.lookup (ofString "decode_blob_hashes") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_blob_hashes,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_blobHashes_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_blob_hashes") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_blob_hashes) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_transaction_blob_decode] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "bh") (ofString "decode_blob_hashes") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_decode_blob_hashes) transactionBlobFinish callee args lookup run
  have entryWatched : RlpSliceInputPrefix entry watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := watchedValid slot inside
    exact ⟨p,n,item.after_frame state entry watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have bodyWatched := blobHashes_body_returned_whole_input_outer_prefix entry bodyPost pointer length input inputLength scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound inputBound starts ends limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayBeforeFrame arrayAligned
    (by change blobHashesBodyCost inputLength.toNat ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget)
    watchedArray watchedCount watchedInput watchedLength entryWatched watchedBeforeFrame watchedBeforeArray value bodyRun
  obtain ⟨records,count,rfl⟩ := value_two_words_of_checked_shape value checked.1
  let resumed := setVarHOLFinite (ofString "bh") (.rStruct [.val (.word records),.val (.word count)]) {bodyPost with locals := state.locals}
  have retained : RlpSliceInputPrefix resumed watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := bodyWatched slot inside
    exact ⟨p,n,item.after_frame bodyPost resumed watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have atTx : resumed.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "bh" ≠ ofString "tx" by decide] using txLocal
  have atResult : resumed.locals.lookup (ofString "bh") = some (.rStruct [.val (.word records),.val (.word count)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have stored := transaction_pair_finish_outer_prefix resumed (ofString "bh") tx records count 256 264 2 watchedArray watchedCount watchedInput watchedLength
    atTx atResult retained beforeTx (by change tx.toNat + 256 < 2^64; omega) headerFits
  rw [← source_transaction_blob_finish_pair] at stored
  change evaluateHOLFiniteState resumed transactionBlobFinish = (none,output) at tailRun
  rw [tailRun] at stored
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := stored slot inside
  exact ⟨p,n,item.after_frame output _ watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩

#print axioms transaction_blob_decode_normal_outer_prefix
end InitECandidate.Runtime
