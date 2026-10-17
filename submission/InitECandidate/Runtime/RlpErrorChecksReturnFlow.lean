import InitECandidate.Runtime.RlpErrorChecks
import InitECandidate.Runtime.RlpErrorCheckFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Successful return through any original RLP error-check list executes
the tail in the initial state: passing checks perform no mutations. -/
theorem evaluate_rlp_error_checks_returned_tail {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (checks : List (ExpHOL 64 × BitVec 64)) (tail : ProgHOL 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (rlpErrorChecks checks tail) = (some (.returned value),post)) :
    evaluateHOLFiniteState state tail = (some (.returned value),post) := by
  induction checks with
  | nil => exact run
  | cons check rest ih =>
    obtain ⟨result,middle,checked,normal,noReturn⟩ := evaluate_rlp_error_check_flow state check.1 check.2 code
    change evaluateHOLFiniteState state (.seq
      (.ite check.1 (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "rlp_fail") [.const check.2]) .skip)
      (rlpErrorChecks rest tail)) = _ at run
    rw [evaluateHOLFiniteState_seq_line780,checked] at run
    cases result with
    | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
    | none =>
      have same := normal rfl
      subst middle
      exact ih run

#print axioms evaluate_rlp_error_checks_returned_tail
end InitECandidate.Runtime
