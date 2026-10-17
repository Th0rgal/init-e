import InitECandidate.Runtime.RlpValidationPublicCallBound
import InitECandidate.Runtime.RlpValidationWrapperGlobals
import InitECandidate.Runtime.PanDiscardNormalBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normal original validator call restores its entry scratch pointer and
retains its frame pointer at the actual caller boundary. -/
theorem rlpValidation_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : (2 * length.toNat + 1) * 15 + 5 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_validate_items") arguments) = (none,post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_validate_items") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_validate_items,.one) := by
    rw [code]; exact originalRuntimeCode_rlpValidation_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_validate_items")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_validate_items) .one pointer length (by decide) installed
  obtain ⟨value,output,bodyRun,globals,_⟩ := evaluate_discard_normal_body state post (ofString "rlp_validate_items")
    arguments [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_validate_items)
    callee .one args lookup run
  rw [globals]
  exact rlpValidation_wrapper_returned_globals entry output pointer length scratch frame ceiling inputLimit pointerLocal lengthLocal
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change (2 * length.toNat + 1) * 15 + 4 ≤ state.clock - 1; omega) value bodyRun

#print axioms rlpValidation_call_normal_globals
end InitECandidate.Runtime
