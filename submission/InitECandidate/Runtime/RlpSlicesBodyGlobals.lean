import InitECandidate.Runtime.RlpListCountBodyNamedGlobal
import InitECandidate.Runtime.RlpSlicesBodyBound
import InitECandidate.Runtime.RlpSlicesAllocationGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every successful original slice-builder result has a slice count bounded
by the supplied input length, including nested validation and allocation. -/
theorem rlpSlices_body_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post)) :
    ∃ count : BitVec 64, value = .rStruct [.val (.word array),.val (.word count)] ∧ count.toNat ≤ length.toNat ∧
      RlpSlicePrefix post array count.toNat ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd array (count * 16)))) ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      array.toNat + count.toNat * 16 ≤ 33806089496 ∧
      (allocationEnd array (count * 16)).toNat ≤ 33806089496 ∧
      (allocationEnd array (count * 16)).toNat % 8 = 0 := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "p"),.var .local (ofString "len")] = some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength]
  have installed : state.code.lookup (ofString "rlp_list_count") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_count,.one) := by
    rw [code]; exact originalRuntimeCode_rlpListCount_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_count")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_list_count) .one pointer length (by decide) installed
  rw [source_rlpSlices_body] at run
  obtain ⟨countValue,bodyPost,ready,output,bodyRun,locals,readyGlobals,clock,readyDomain,_,readyCode,tail,restored⟩ :=
    evaluate_decCall_returned_global_clock_scope state post (ofString "count") (ofString "rlp_list_count") .one .one
      _ _ (sourceFunctionBody Guest.guestFn_rlp_list_count) rlpSlicesAllocation callee value args lookup run
  obtain ⟨count,rfl,countBound,countScratch,countFrame⟩ := rlpListCount_body_returned_contract entry bodyPost pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock - 1; omega) countValue bodyRun
  have bound := evaluate_rlpListCount_body_bounded entry pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock - 1; omega)
  rw [bodyRun] at bound
  dsimp only at bound
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_count)
  rw [bodyRun] at metadata
  dsimp only at metadata
  let resumed := setVarHOLFinite (ofString "count") (.val (.word count)) ready
  have pLocal : resumed.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "count" ≠ ofString "p" by decide] using atPointer
  have cLocal : resumed.locals.lookup (ofString "count") = some (.val (.word count)) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enough : count.toNat * 12 + 2 ≤ resumed.clock := by
    change count.toNat * 12 + 2 ≤ ready.clock
    have cost : state.clock - 1 ≤ bodyPost.clock + length.toNat * ((2 * length.toNat + 1) * 15 + 19) := bound.1
    omega
  have heapFrame := rlpListCount_body_returned_named_global entry bodyPost (ofString "heap_ptr") (by decide)
    pointer length scratch frame ceiling inputLimit pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock - 1; omega) (.val (.word count)) bodyRun
  have atHeap : resumed.globals.lookup (ofString "heap_ptr") = some (.val (.word array)) := by
    change ready.globals.lookup _ = _
    rw [readyGlobals,heapFrame]
    exact heap
  have resumedArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → resumed.memaddrs address := by
    intro address lower upper
    change ready.memaddrs address
    rw [readyDomain,metadata.2.1]
    exact heapArena address lower upper
  obtain ⟨returned,filled,allocatedGlobals⟩ := rlpSlices_allocation_return_globals resumed output pointer count array pLocal cLocal atHeap arrayBound
    (by omega) resumedArena (readyCode.trans (metadata.1.trans code)) enough value tail
  let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "count"),.const 16]
  have allocArgs : evalListHOLFinite resumed (h := fun address => Classical.propDecidable (resumed.memaddrs address)) [argument] =
      some [.val (.word (count * 16))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,cLocal,panOpHOL,valueIsWord,valueWord]
  have called : evaluateHOLFiniteState resumed (.decCall (ofString "arr") .one (ofString "alloc") [argument] rlpSlicesInitialized) =
      (some (.returned value),output) := by simpa only [source_rlpSlices_allocation,argument] using tail
  have request := alloc_declaration_returned_request resumed output argument array (count * 16) (ofString "arr") .one
    rlpSlicesInitialized value allocArgs (readyCode.trans (metadata.1.trans code)) atHeap called
  have interval := rlpSlices_allocation_interval array count arrayBound (by omega) request
  have endpoint := allocationEnd_within_heap array (count * 16) arrayBound request
  have product : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
    rfl
  have covers := allocationEnd_covers array (count * 16) (by rw [product]; exact interval)
  refine ⟨count,returned,countBound,?_,?_,?_,?_,interval,endpoint,covers.2.2⟩
  · rw [restored]
    intro slot inside
    obtain ⟨p,n,item⟩ := filled slot inside
    exact ⟨p,n,RlpSliceEntry.after_frame output _ _ _ _ _ item rfl rfl rfl⟩
  · rw [restored]
    change output.globals.lookup _ = _
    rw [allocatedGlobals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [restored]
    change output.globals.lookup _ = _
    rw [allocatedGlobals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,resumed,setVarHOLFinite,readyGlobals,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide] using countScratch
  · rw [restored]
    change output.globals.lookup _ = _
    rw [allocatedGlobals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,resumed,setVarHOLFinite,readyGlobals,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide] using countFrame

#print axioms rlpSlices_body_returned_globals
end InitECandidate.Runtime
