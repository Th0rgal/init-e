import InitECandidate.Runtime.RlpValidationCleanupTerminal
import InitECandidate.Runtime.PanHandledNoReturn
import InitECandidate.Runtime.DiscardCallNoReturn
import InitECandidate.Runtime.TrapNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpValidation_cleanup_no_return {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state rlpValidationCleanupHandler).1 ≠ some (.returned value) := by
  rw [source_rlpValidation_cleanup_handler]
  apply evaluate_sequence_no_return
  · exact evaluate_discard_call_no_return state _ _ value
  · intro next
    exact evaluate_raise_no_return next _ _ value

theorem evaluate_rlpValidation_handled_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.call (some (none,some (ofString "RlpErr",ofString "e",rlpValidationCleanupHandler)))
      (ofString "_rlp_validate_items_body") arguments)).1 ≠ some (.returned value) :=
  evaluate_handled_discard_no_return state _ _ _ arguments _ evaluate_rlpValidation_cleanup_no_return value

#print axioms evaluate_rlpValidation_handled_no_return
end InitECandidate.Runtime
