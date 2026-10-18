import InitECandidate.Runtime.RlpSlicesBodyHeapInputContract
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.RlpSlicesBodyOuterRuntimeContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual slice declaration reaches its continuation with the returned
array entries bounded by the supplied input, while retaining older heap slices
above the scratch ceiling and below the new allocation. -/
theorem evaluate_rlpSlices_returned_declaration_heap_runtime_input_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 ≤ state.clock)
    (older olderCount input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state older input inputLength olderCount.toNat)
    (before : older.toNat + olderCount.toNat * 16 ≤ array.toNat)
    (olderAboveScratch : ceiling ≤ older.toNat)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (.decCall name (.comb [.one,.one]) (ofString "rlp_list_to_slices") arguments continuation) = (some (.returned finalValue),post)) :
    ∃ (count : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      count.toNat ≤ length.toNat ∧ ready.locals = state.locals ∧ RlpSliceInputPrefix ready array pointer length count.toNat ∧
      RlpSliceInputPrefix ready older input inputLength olderCount.toNat ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd array (count * 16)))) ∧
      ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      state.clock ≤ ready.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4) ∧
      ready.clock ≤ state.clock ∧
      array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
      (allocationEnd array (count * 16)).toNat ≤ 33806089496 ∧
      (allocationEnd array (count * 16)).toNat % 8 = 0 ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word array),.val (.word count)]) ready) continuation = (some (.returned finalValue),output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
  obtain ⟨value,bodyPost,ready,output,bodyRun,locals,memory,globals,clock,domain,_,readyCode,tail,restored⟩ := evaluate_decCall_returned_global_memory_clock_scope state post name
    (ofString "rlp_list_to_slices") (.comb [.one,.one]) (.comb [.one,.one]) arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) continuation callee finalValue args lookup run
  have entryValid : RlpSliceInputPrefix entry older input inputLength olderCount.toNat := by
    intro index inside
    obtain ⟨pointer,length,item⟩ := valid index inside
    exact ⟨pointer,length,RlpSliceInputEntry.after_frame state entry older index pointer length input inputLength item rfl rfl rfl⟩
  obtain ⟨count,shape,bounded,filled,preserved⟩ := rlpSlices_body_returned_heap_input_contract entry bodyPost pointer length scratch frame array ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap arrayBound countLimit heapArena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock - 1; omega) older olderCount input inputLength entryValid before olderAboveScratch inputBeforeFrame inputBeforeArray value bodyRun
  have ticks : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ entry.clock := by
    change _ ≤ state.clock - 1
    omega
  obtain ⟨runtimeCount,runtimeShape,_,_,heapPost,scratchPost,framePost,_,covered,endpoint,aligned⟩ :=
    rlpSlices_body_returned_outer_runtime_contract entry bodyPost pointer length scratch frame array pointer length ceiling inputLimit
      pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
      arena heap arrayBound countLimit heapArena ticks inputBeforeFrame inputBeforeArray (Nat.le_refl _) (Nat.le_refl _) value bodyRun
  have equal : count = runtimeCount := by
    have shapes := shape.symm.trans runtimeShape
    simpa only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,and_true,true_and] using shapes
  subst runtimeCount
  have boundedBody := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks
  rw [bodyRun] at boundedBody
  dsimp only at boundedBody
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [bodyRun] at metadata
  subst value
  have readable : RlpSliceInputPrefix ready array pointer length count.toNat := by
    intro slot inside
    obtain ⟨p,n,entry⟩ := filled slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame bodyPost ready _ _ _ _ _ _ entry domain (congrFun memory _) (congrFun memory _)⟩
  have retained : RlpSliceInputPrefix ready older input inputLength olderCount.toNat := by
    intro index inside
    obtain ⟨pointer,length,item⟩ := preserved index inside
    exact ⟨pointer,length,RlpSliceInputEntry.after_frame bodyPost ready older index pointer length input inputLength item domain
      (congrFun memory _) (congrFun memory _)⟩
  have remaining : ready.clock ≤ state.clock := by
    rw [clock]
    exact boundedBody.2.1.trans (Nat.sub_le _ _)
  have consumed : state.clock ≤ ready.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4) := by
    have debit : state.clock - 1 ≤ bodyPost.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3) := boundedBody.1
    rw [clock]
    omega
  exact ⟨count,ready,output,bounded,locals,readable,retained,
    by rw [globals]; exact heapPost,by rw [globals]; exact scratchPost,by rw [globals]; exact framePost,
    readyCode.trans metadata.1,domain.trans metadata.2.1,consumed,remaining,covered,endpoint,aligned,tail,restored⟩

#print axioms evaluate_rlpSlices_returned_declaration_heap_runtime_input_contract
end InitECandidate.Runtime
