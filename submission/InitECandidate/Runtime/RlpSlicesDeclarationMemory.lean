import InitECandidate.Runtime.RlpSlicesBodyMemory
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.PanDecCallNormalBodyScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual slice declaration reaches its continuation with the returned
array readable in concrete memory and with an input-bounded count. -/
theorem evaluate_rlpSlices_declaration_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState state (.decCall name (.comb [.one,.one]) (ofString "rlp_list_to_slices") arguments continuation) = (none,post)) :
    ∃ (count : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      count.toNat ≤ length.toNat ∧ ready.locals = state.locals ∧ RlpSlicePrefix ready array count.toNat ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word array),.val (.word count)]) ready) continuation = (none,output) ∧
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
  obtain ⟨value,bodyPost,ready,output,bodyRun,locals,memory,domain,_,tail,restored⟩ := evaluate_decCall_normal_body_scope state post name
    (ofString "rlp_list_to_slices") (.comb [.one,.one]) (.comb [.one,.one]) arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) continuation callee args lookup run
  obtain ⟨count,shape,bounded,filled⟩ := rlpSlices_body_returned_memory entry bodyPost pointer length scratch frame array ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap arrayBound countLimit heapArena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock - 1; omega) value bodyRun
  subst value
  have readable : RlpSlicePrefix ready array count.toNat := by
    intro slot inside
    obtain ⟨p,n,entry⟩ := filled slot inside
    exact ⟨p,n,RlpSliceEntry.after_frame bodyPost ready _ _ _ _ entry domain (congrFun memory _) (congrFun memory _)⟩
  exact ⟨count,ready,output,bounded,locals,readable,tail,restored⟩

#print axioms evaluate_rlpSlices_declaration_memory
end InitECandidate.Runtime
