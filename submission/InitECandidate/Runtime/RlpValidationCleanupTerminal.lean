import InitECandidate.Runtime.RlpValidationCleanupBound
import InitECandidate.Runtime.PanHandledNormalLocals
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual catch handler either fails in release or rethrows; it never
falls through into the wrapper's normal scratch-release path. -/
theorem evaluate_rlpValidation_cleanup_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state rlpValidationCleanupHandler).1 ≠ none := by
  rw [source_rlpValidation_cleanup_handler,evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "mark")]) with
  | mk result post =>
    cases result with
    | none => exact evaluate_raise_terminal post (ofString "RlpErr") (.var .local (ofString "e"))
    | some result => simp

/-- Normal completion of the original handled validator call retains all
caller locals, in particular the saved scratch mark. -/
theorem evaluate_rlpValidation_handled_normal_locals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64))
    (run : evaluateHOLFiniteState state
      (.call (some (none,some (ofString "RlpErr",ofString "e",rlpValidationCleanupHandler)))
        (ofString "_rlp_validate_items_body") arguments) = (none,post)) :
    post.locals = state.locals :=
  evaluate_handled_normal_locals state post (ofString "_rlp_validate_items_body") (ofString "RlpErr")
    (ofString "e") arguments rlpValidationCleanupHandler evaluate_rlpValidation_cleanup_terminal run

#print axioms evaluate_rlpValidation_cleanup_terminal
#print axioms evaluate_rlpValidation_handled_normal_locals
end InitECandidate.Runtime
