import InitECandidate.Runtime.AccessListStepBound
import InitECandidate.Runtime.AccessListItemCheckHeapProgress
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_step_heap_progress {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) accessStepArguments =
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
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (wholeInputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : accessStepCost length.toNat inputLength.toNat ≤ state.clock)
    (outerIndex : BitVec 64)
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (run : evaluateHOLFiniteState state accessStep = (none,final)) :
    final.locals.lookup (ofString "i") = some (.val (.word (outerIndex + 1))) ∧
      final.locals.lookup (ofString "lst") = state.locals.lookup (ofString "lst") ∧
      final.locals.lookup (ofString "recs") = state.locals.lookup (ofString "recs") := by
  let first := length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632
  let tailCost := accessInnerSlicesCost inputLength.toNat inputLength.toNat
  have totalBudget : first + 1 + tailCost ≤ state.clock := by
    simpa only [first,tailCost,accessStepCost,← Nat.add_assoc] using budget
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : first ≤ entry.clock := by
    change first ≤ state.clock - 1
    exact authorization_inner_entry_budget first tailCost state.clock totalBudget
  have bounded := evaluate_rlpItem_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  have installed : state.code.lookup (ofString "rlp_item") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
  rw [source_access_step] at run
  obtain ⟨value,post,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "it") (ofString "rlp_item") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_rlp_item) accessItemCheck callee args lookup run
  rw [bodyRun] at bounded
  have bodyCost : state.clock - 1 ≤ post.clock + first := bounded.1
  obtain ⟨kind,payloadPointer,payload,consumed,shape,starts,ends,payloadNoWrap,payloadBound,scratchPost,framePost,heapSame⟩ :=
    rlpItem_body_returned_runtime_contract entry post pointer length scratch frame ceiling inputLimit atPointer atLength
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget value bodyRun
  subst value
  let resumed := setVarHOLFinite (ofString "it")
    (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]) {post with locals := state.locals}
  have atItem : resumed.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [bodyRun] at metadata
  have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
    intro address lower upper
    change post.memaddrs address
    rw [metadata.2.1]
    exact arena address lower upper
  have resumedHeapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → resumed.memaddrs address := by
    intro address lower upper
    change post.memaddrs address
    rw [metadata.2.1]
    exact heapArena address lower upper
  have tailBudget : tailCost ≤ resumed.clock := by
    change tailCost ≤ post.clock
    exact blobHashes_budget_transfer first tailCost tailCost state.clock post.clock (Nat.le_refl _) totalBudget bodyCost
  have insideInput : payload.toNat ≤ inputLength.toNat := by omega
  have costBound := accessInnerSlicesCost_mono_left payload.toNat inputLength.toNat inputLength.toNat insideInput
  have resumedIndex : resumed.locals.lookup (ofString "i") = some (.val (.word outerIndex)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "it" ≠ ofString "i" by decide] using binding
  have next := access_item_check_heap_progress resumed output kind payloadPointer payload consumed
    input inputLength scratch frame array ceiling inputLimit atItem payloadNoWrap
    (Nat.le_trans payloadBound lengthBound) inputBound limitBound (Nat.le_trans inputStarts starts) (Nat.le_trans ends inputEnds)
    scratchPost framePost (metadata.1.trans code) orderedFrame framePositive scratchBelow resumedArena (heapSame.trans heap)
    arrayBound countLimit resumedHeapArena (Nat.le_trans ends inputBeforeFrame) (Nat.le_trans ends inputBeforeArray)
    arrayAbove
    wholeInputBeforeArray wholeInputBeforeFrame (Nat.le_trans costBound tailBudget) outerIndex resumedIndex tailRun
  rw [restored]
  refine ⟨?_,?_,?_⟩
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "it",state.locals.lookup (ofString "it"))).lookup (ofString "i") = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact next.1
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "it",state.locals.lookup (ofString "it"))).lookup (ofString "lst") = _
    rw [restore_other_local _ _ _ _ (by decide),next.2.1]
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "it" ≠ ofString "lst" by decide]
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "it",state.locals.lookup (ofString "it"))).lookup (ofString "recs") = _
    rw [restore_other_local _ _ _ _ (by decide),next.2.2]
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "it" ≠ ofString "recs" by decide]

#print axioms access_step_heap_progress
end InitECandidate.Runtime
