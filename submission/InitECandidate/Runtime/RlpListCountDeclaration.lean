import InitECandidate.Runtime.RlpListCountDeclarationBound
import InitECandidate.Runtime.RlpListCountBodyResult
import InitECandidate.Runtime.PanDecCallNormalGlobalClockScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal original list-count declarations bind an input-bounded count with
caller locals and scratch/frame globals retained at continuation entry. -/
theorem evaluate_rlpListCount_declaration_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "rlp_list_count") arguments continuation) = (none,post)) :
    ∃ (count : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      count.toNat ≤ length.toNat ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word count)) ready) continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_list_count") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_count,.one) := by
    rw [code]; exact originalRuntimeCode_rlpListCount_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_count")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_list_count) .one pointer length (by decide) installed
  obtain ⟨value,bodyPost,ready,output,bodyRun,locals,globals,_,_,_,_,tail,restored⟩ := evaluate_decCall_normal_global_clock_scope state post name
    (ofString "rlp_list_count") .one .one arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_list_count) continuation callee args lookup run
  obtain ⟨count,shape,bounded,scratchPost,framePost⟩ := rlpListCount_body_returned_contract entry bodyPost pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock - 1; omega) value bodyRun
  subst value
  exact ⟨count,ready,output,bounded,locals,by rw [globals]; exact scratchPost,by rw [globals]; exact framePost,tail,restored⟩

#print axioms evaluate_rlpListCount_declaration_contract
end InitECandidate.Runtime
