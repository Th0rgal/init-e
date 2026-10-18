import InitECandidate.Runtime.RlpSlicesBodyOuterPrefix
import InitECandidate.Runtime.RlpSliceInputPrefixOuter
import InitECandidate.Runtime.BlobHashesBodyBound
import InitECandidate.Runtime.BlobHashesAllocationIndependentOuterPrefix
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful blob decoding preserves a distinct earlier transaction field array. -/
theorem blobHashes_body_returned_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
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
    (arrayBeforeFrame : array.toNat + length.toNat * 16 ≤ frame.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 +
      (length.toNat * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) + 2) ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (watchedBeforeArray : watchedArray.toNat + watchedCount.toNat * 16 ≤ array.toNat)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_blob_hashes) = (some (.returned finalValue),final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ entry.clock := by
    change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock - 1
    omega
  have bounded := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_blobHashes_body] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_returned_exact_scope state final
    (ofString "lst") (ofString "rlp_list_to_slices") (.comb [.one,.one]) (.comb [.one,.one]) arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) blobHashesAfterSlices callee
    finalValue args lookup run
  rw [bodyRun] at bounded
  have actual := bodyRun
  obtain ⟨count,shape,countBound,slices,heapPost,scratchPost,framePost,interval,endpoint,aligned⟩ :=
    rlpSlices_body_returned_runtime_contract entry bodyPost pointer length scratch frame array ceiling inputLimit
      atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      heap arrayBound (by omega) heapArena entryBudget inputBeforeFrame inputBeforeArray value actual
  subst value
  let resumed := setVarHOLFinite (ofString "lst") (.rStruct [.val (.word array),.val (.word count)]) {bodyPost with locals := state.locals}
  have listLocal : resumed.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have resumedSlices : RlpSliceInputPrefix resumed array pointer length count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := slices slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame bodyPost resumed array slot p n pointer length item rfl rfl rfl⟩
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [actual] at metadata
  have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
    intro address lower upper
    change bodyPost.memaddrs address
    rw [metadata.2.1]
    exact arena address lower upper
  have product : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
    rfl
  have covers := allocationEnd_covers array (count * 16) (by rw [product]; exact interval)
  have factor := Nat.mul_le_mul_right (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) countBound
  have tailBudget : count.toNat * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) + 2 ≤ resumed.clock := by
    change count.toNat * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) + 2 ≤ bodyPost.clock
    have cost := bounded.1
    change state.clock - 1 ≤ bodyPost.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3) at cost
    apply blobHashes_budget_transfer _ _ _ state.clock bodyPost.clock (Nat.add_le_add_right factor 2) _ cost
    simpa only [← Nat.add_assoc] using budget
  have nextNat : (allocationEnd array (count * 16)).toNat = array.toNat + count.toNat * 16 := by
    have sizeAligned : (count * 16).toNat % 8 = 0 := by rw [product]; omega
    rw [allocationEnd_aligned_toNat array (count * 16) (by rw [product]; exact interval) arrayAligned sizeAligned,product]
  have entryWatched : RlpSliceInputPrefix entry watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := watchedValid slot inside
    exact ⟨p,n,item.after_frame state entry watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have bodyWatched := rlpSlices_body_returned_outer_prefix entry bodyPost pointer length scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap arrayBound (by omega) heapArena entryBudget _ bodyRun watchedArray watchedCount watchedInput watchedLength entryWatched watchedBeforeArray watchedBeforeFrame
  have resumedWatched : RlpSliceInputPrefix resumed watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := bodyWatched slot inside
    exact ⟨p,n,item.after_frame bodyPost resumed watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have retained := blobHashes_allocation_returned_independent_outer_prefix resumed output array count (allocationEnd array (count * 16)) input inputLength scratch frame ceiling inputLimit
    listLocal (resumedSlices.within_outer resumed array pointer length input inputLength _ starts ends) scratchPost framePost
    (metadata.1.trans code) resumedArena inputBound limitBound orderedFrame framePositive
    scratchBelow (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right 16 countBound) _) arrayBeforeFrame)
    (by rw [product] at covers; exact covers.1) aligned heapPost endpoint (by omega)
    tailBudget
    watchedArray watchedCount watchedInput watchedLength resumedWatched watchedBeforeFrame (by rw [nextNat]; omega) finalValue tailRun
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame output _ watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩

#print axioms blobHashes_body_returned_independent_outer_prefix
end InitECandidate.Runtime
