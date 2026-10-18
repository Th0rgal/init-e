import InitECandidate.Runtime.AccessListEntryCheckArity
import InitECandidate.Runtime.AccessListInnerSlicesBound
import InitECandidate.Runtime.AccessListEntryCheckRuntimeContract
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_inner_slices_runtime_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))] =
        some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (inputStarts : input.toNat ≤ pointer.toNat)
    (inputEnds : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
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
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (reserve : array.toNat + length.toNat * 16 + 7 + inputLength.toNat * 16 ≤ frame.toNat)
    (budget : accessInnerSlicesCost length.toNat inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state accessInnerSlices = (none,final)) :
    ∃ slotCount : BitVec 64, slotCount.toNat ≤ inputLength.toNat ∧
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)))) ∧
      final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      array.toNat + 32 + slotCount.toNat * 48 ≤ (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)).toNat ∧
      (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)).toNat ≤ array.toNat + slotCount.toNat * 48 + 46 ∧
      (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)).toNat ≤ 33806089496 ∧ (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)).toNat % 8 = 0 := by
  let first := length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3
  let tailCost := ((inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) + accessSlotItemCost inputLength.toNat)
  have total : first + 1 + tailCost ≤ state.clock := by
    simpa only [first,tailCost,accessInnerSlicesCost,← Nat.add_assoc] using budget
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : first ≤ entry.clock := by
    change first ≤ state.clock - 1
    exact authorization_inner_entry_budget first tailCost state.clock total
  have bounded := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_access_inner_slices] at run
  obtain ⟨value,post,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "ent") (ofString "rlp_list_to_slices") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) accessEntryCheck callee args lookup run
  rw [bodyRun] at bounded
  have bodyCost : state.clock - 1 ≤ post.clock + first := bounded.1
  obtain ⟨count,shape,countBound,slices,heapPost,scratchPost,framePost,interval,endpoint,aligned⟩ :=
    rlpSlices_body_returned_runtime_contract entry post pointer length scratch frame array ceiling inputLimit
      atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena heap arrayBound (by omega) heapArena entryBudget inputBeforeFrame inputBeforeArray value bodyRun
  subst value
  have outerSlices := slices.within_outer post array pointer length input inputLength count.toNat inputStarts inputEnds
  let resumed := setVarHOLFinite (ofString "ent") (.rStruct [.val (.word array),.val (.word count)]) {post with locals := state.locals}
  have resumedPrefix : RlpSliceInputPrefix resumed array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerSlices slot inside
    exact ⟨p,n,item.after_frame post resumed array slot p n input inputLength rfl rfl rfl⟩
  have atEntry : resumed.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [bodyRun] at metadata
  have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
    intro address lower upper
    change post.memaddrs address
    rw [metadata.2.1]
    exact arena address lower upper
  have tailBudget : tailCost ≤ resumed.clock := by
    change tailCost ≤ post.clock
    exact blobHashes_budget_transfer first tailCost tailCost state.clock post.clock (Nat.le_refl _) total bodyCost
  have product : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
    rfl
  have covers := allocationEnd_covers array (count * 16) (by rw [product]; exact interval)
  rw [product] at covers
  have resumedHeapArena : ∀ address : BitVec 64, (allocationEnd array (count * 16)).toNat ≤ address.toNat →
      address.toNat < 33806089496 → resumed.memaddrs address := by
    intro address lower upper
    change post.memaddrs address
    rw [metadata.2.1]
    exact heapArena address (by omega) upper
  have next := access_entry_check_runtime_contract resumed output array count input inputLength scratch frame (allocationEnd array (count * 16))
    ceiling inputLimit atEntry resumedPrefix inputBound limitBound scratchPost framePost (metadata.1.trans code)
    orderedFrame framePositive scratchBelow resumedArena
    (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right 16 countBound) _) arrayBeforeFrame)
    heapPost endpoint countLimit resumedHeapArena (by omega) (by omega) tailBudget tailRun
  have two := access_entry_check_normal_arity resumed output array count atEntry tailRun
  have firstBounds := covers
  have nextRuntime := next
  rw [two] at nextRuntime firstBounds
  simp only [show (2#64 * (16 : BitVec 64)) = (32 : BitVec 64) by decide] at nextRuntime
  have firstBounds32 : array.toNat + 32 ≤ (allocationEnd array 32).toNat ∧
      (allocationEnd array 32).toNat < array.toNat + 40 := by
    constructor
    · simpa using firstBounds.1
    · simpa using firstBounds.2.1
  obtain ⟨slotCount,slotBound,heapFinal,scratchFinal,frameFinal,low,high,endBound,endAligned⟩ := nextRuntime
  rw [restored]
  refine ⟨slotCount,slotBound,?_,scratchFinal,frameFinal,?_,?_,?_,?_⟩
  · simpa using heapFinal
  · change array.toNat + 32 + slotCount.toNat * 48 ≤ _
    have lower := firstBounds32.1
    omega
  · have upper := firstBounds32.2
    omega
  · simpa using endBound
  · simpa using endAligned

#print axioms access_inner_slices_runtime_contract
end InitECandidate.Runtime
