import InitECandidate.Runtime.AccessListBodyHeapBound
import InitECandidate.Runtime.AccessListAllocationHeapRuntimeContract
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete successful decoding exposes its real slices, returned record array and final heap. -/
theorem access_body_returned_heap_runtime_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
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
    (budget : accessBodyCost length.toNat ≤ state.clock)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_access_list) = (some (.returned finalValue),final)) :
    ∃ count heap : BitVec 64,
      count.toNat ≤ length.toNat ∧
      finalValue = .rStruct [.val (.word (allocationEnd array (count * 16))),.val (.word count)] ∧
      RlpSliceInputPrefix final array pointer length count.toNat ∧
      final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      heap.toNat ≤ 33806089496 ∧ heap.toNat % 8 = 0 ∧
      pointer.toNat + length.toNat ≤ heap.toNat ∧
      (allocationEnd array (count * 16)).toNat + count.toNat * 24 ≤ heap.toNat := by
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
    dsimp [accessBodyCost] at budget
    omega
  have bounded := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_access_body] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_returned_exact_scope state final
    (ofString "lst") (ofString "rlp_list_to_slices") (.comb [.one,.one]) (.comb [.one,.one]) arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) accessAfterSlices callee
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
  have factor := Nat.mul_le_mul_right (accessStepCost length.toNat length.toNat + 1) countBound
  have tailBudget : count.toNat * (accessStepCost length.toNat length.toNat + 1) + 2 ≤ resumed.clock := by
    change count.toNat * (accessStepCost length.toNat length.toNat + 1) + 2 ≤ bodyPost.clock
    have cost := bounded.1
    change state.clock - 1 ≤ bodyPost.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3) at cost
    exact access_after_slices_budget length.toNat count.toNat state.clock bodyPost.clock countBound budget cost
  have nextNat : (allocationEnd array (count * 16)).toNat = array.toNat + count.toNat * 16 := by
    have sizeAligned : (count * 16).toNat % 8 = 0 := by rw [product]; omega
    rw [allocationEnd_aligned_toNat array (count * 16) (by rw [product]; exact interval) arrayAligned sizeAligned,product]
  have resumedHeapArena : ∀ address : BitVec 64, (allocationEnd array (count * 16)).toNat ≤ address.toNat →
      address.toNat < 33806089496 → resumed.memaddrs address := by
    intro address lower upper
    change bodyPost.memaddrs address
    rw [metadata.2.1]
    exact heapArena address (by rw [nextNat] at lower; omega) upper
  have tail := access_allocation_returned_heap_runtime_contract resumed output array count (allocationEnd array (count * 16)) pointer length scratch frame ceiling inputLimit
    listLocal resumedSlices scratchPost framePost (metadata.1.trans code) resumedArena lengthBound limitBound orderedFrame framePositive
    scratchBelow arrayAbove
    (by rw [product] at covers; exact covers.1) aligned heapPost endpoint
    (by omega)
    resumedHeapArena (by omega) (by rw [nextNat]; omega) inputBeforeFrame tailBudget
    finalValue tailRun
  obtain ⟨resultShape,nextHeap,retained,scratchFinal,frameFinal,heapFinal,heapLimit,endAligned,inputBefore,recordsBefore⟩ := tail
  rw [restored]
  refine ⟨count,nextHeap,countBound,resultShape,?_,scratchFinal,frameFinal,heapFinal,heapLimit,endAligned,inputBefore,recordsBefore⟩
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame output _ array slot p n pointer length rfl rfl rfl⟩

#print axioms access_body_returned_heap_runtime_contract
end InitECandidate.Runtime
