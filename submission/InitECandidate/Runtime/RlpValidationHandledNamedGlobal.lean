import InitECandidate.Runtime.RlpValidationHandledCallBound
import InitECandidate.Runtime.RlpValidationBodyNamedGlobal
import InitECandidate.Runtime.RlpValidationCleanupTerminal
import InitECandidate.Runtime.PanHandledNormalBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal original handled validation retains frame_mem_ptr from its actual
successful callee execution; the catch handler cannot complete normally. -/
theorem rlpValidation_handled_normal_named_global {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
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
    (budget : (2 * length.toNat + 1) * 15 + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,some (ofString "RlpErr",ofString "e",rlpValidationCleanupHandler)))
      (ofString "_rlp_validate_items_body") arguments) = (none,post)) :
    post.globals.lookup watched = state.globals.lookup watched := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "_rlp_validate_items_body") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn__rlp_validate_items_body,.one) := by
    rw [code]; exact originalRuntimeCode_rlpValidationBody_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "_rlp_validate_items_body")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) .one pointer length (by decide) installed
  obtain ⟨value,output,bodyRun,globals,_⟩ := evaluate_handled_normal_body state post (ofString "_rlp_validate_items_body")
    (ofString "RlpErr") (ofString "e") arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) rlpValidationCleanupHandler callee .one args lookup
    evaluate_rlpValidation_cleanup_terminal run
  rw [globals]
  exact rlpValidation_body_returned_named_global entry output watched different pointer length scratch frame ceiling inputLimit pointerLocal lengthLocal
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change (2 * length.toNat + 1) * 15 ≤ state.clock - 1; omega) value bodyRun

#print axioms rlpValidation_handled_normal_named_global
end InitECandidate.Runtime
