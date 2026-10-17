import InitECandidate.Runtime.PanWhileNoReturn
import InitECandidate.Runtime.RlpValidationStepNoReturn
import InitECandidate.Runtime.RlpValidationLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The original validator loop cannot bypass the body's final return-zero. -/
theorem evaluate_rlpValidation_loop_no_return {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state rlpValidationLoop).1 ≠ some (.returned value) :=
  evaluate_while_no_return _ _ evaluate_rlpValidation_step_no_return state value

#print axioms evaluate_rlpValidation_loop_no_return
end InitECandidate.Runtime
