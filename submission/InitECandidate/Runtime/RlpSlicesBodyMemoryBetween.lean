import InitECandidate.Runtime.RlpListCountBodyAbove
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.RlpListCountBodyNamedGlobal
import InitECandidate.Runtime.RlpSlicesBodyBound
import InitECandidate.Runtime.RlpSlicesAllocationMemoryBefore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original slicing preserves heap words between the scratch
ceiling and the new allocation base, while constructing readable new slices. -/
theorem rlpSlices_body_returned_memory_between {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
      (∀ watched : BitVec 64, watched.toNat < array.toNat → ceiling ≤ watched.toNat →
        post.memory watched = state.memory watched) := by
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
  obtain ⟨countValue,bodyPost,ready,output,bodyRun,locals,readyMemory,readyGlobals,clock,readyDomain,_,readyCode,tail,restored⟩ :=
    evaluate_decCall_returned_global_memory_clock_scope state post (ofString "count") (ofString "rlp_list_count") .one .one
      _ _ (sourceFunctionBody Guest.guestFn_rlp_list_count) rlpSlicesAllocation callee value args lookup run
  obtain ⟨count,rfl,countBound,_,_⟩ := rlpListCount_body_returned_contract entry bodyPost pointer length scratch frame ceiling inputLimit
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
  obtain ⟨returned,filled,memoryFrame⟩ := rlpSlices_allocation_return_memory_before resumed output pointer count array pLocal cLocal atHeap arrayBound
    (by omega) resumedArena (readyCode.trans (metadata.1.trans code)) enough value tail
  refine ⟨count,returned,countBound,?_,?_⟩
  · rw [restored]
    intro slot inside
    obtain ⟨p,n,entry⟩ := filled slot inside
    exact ⟨p,n,RlpSliceEntry.after_frame output _ _ _ _ _ entry rfl rfl rfl⟩
  · rw [restored]
    intro watched beforeArray aboveScratch
    have kept := memoryFrame watched beforeArray
    have counted := rlpListCount_body_returned_above entry bodyPost pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock - 1; omega)
      (.val (.word count)) bodyRun watched aboveScratch
    change output.memory watched = state.memory watched
    change output.memory watched = ready.memory watched at kept
    rw [kept,readyMemory]
    exact counted

#print axioms rlpSlices_body_returned_memory_between
end InitECandidate.Runtime
