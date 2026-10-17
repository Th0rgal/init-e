import InitECandidate.Runtime.RlpSlicesBodyBound
import InitECandidate.Runtime.RlpSlicesAllocationReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every successful original slice-builder result has a slice count bounded
by the supplied input length, including nested validation and allocation. -/
theorem rlpSlices_body_returned_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post)) :
    ∃ (array : ValueHOL 64) (count : BitVec 64), value = .rStruct [array,.val (.word count)] ∧ count.toNat ≤ length.toNat := by
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
  obtain ⟨countValue,bodyPost,ready,output,bodyRun,locals,_,clock,_,_,readyCode,tail,_⟩ :=
    evaluate_decCall_returned_global_clock_scope state post (ofString "count") (ofString "rlp_list_count") .one .one
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
  obtain ⟨array,returned⟩ := rlpSlices_allocation_return_contract resumed output pointer count pLocal cLocal
    (readyCode.trans (metadata.1.trans code)) enough value tail
  exact ⟨array,count,returned,countBound⟩

#print axioms rlpSlices_body_returned_contract
end InitECandidate.Runtime
