import InitECandidate.Runtime.RlpErrorChecks
import InitECandidate.Runtime.RlpErrorCheckFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned value after RLP checks must come from the continuation in
exactly the original state, even when no source ticks remain. -/
theorem evaluate_rlp_error_checks_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (checks : List (ExpHOL 64 × BitVec 64)) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (rlpErrorChecks checks continuation) = (some (.returned value),post)) :
    evaluateHOLFiniteState state continuation = (some (.returned value),post) := by
  induction checks with
  | nil => exact run
  | cons check rest ih =>
    obtain ⟨result,middle,checked,normal,noReturn⟩ := evaluate_rlp_error_check_flow state check.1 check.2 code
    change evaluateHOLFiniteState state (.seq
      (.ite check.1 (.call (some (none,none)) (ofString "rlp_fail") [.const check.2]) .skip)
      (rlpErrorChecks rest continuation)) = _ at run
    rw [evaluateHOLFiniteState_seq_line780,checked] at run
    cases result with
    | none =>
      have same := normal rfl
      subst middle
      exact ih run
    | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)

/-- A successful checked return certifies that the same checks pass without
changing the state for any replacement continuation. -/
theorem evaluate_rlp_error_checks_replace_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (checks : List (ExpHOL 64 × BitVec 64)) (continuation replacement : ProgHOL 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (rlpErrorChecks checks continuation) = (some (.returned value),post)) :
    evaluateHOLFiniteState state (rlpErrorChecks checks replacement) = evaluateHOLFiniteState state replacement := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
    obtain ⟨result,middle,checked,normal,noReturn⟩ := evaluate_rlp_error_check_flow state check.1 check.2 code
    change evaluateHOLFiniteState state (.seq
      (.ite check.1 (.call (some (none,none)) (ofString "rlp_fail") [.const check.2]) .skip)
      (rlpErrorChecks rest continuation)) = _ at run
    rw [evaluateHOLFiniteState_seq_line780,checked] at run
    change evaluateHOLFiniteState state (.seq
      (.ite check.1 (.call (some (none,none)) (ofString "rlp_fail") [.const check.2]) .skip)
      (rlpErrorChecks rest replacement)) = _
    rw [evaluateHOLFiniteState_seq_line780,checked]
    cases result with
    | none =>
      have same := normal rfl
      subst middle
      exact ih run
    | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)

#print axioms evaluate_rlp_error_checks_replace_returned
#print axioms evaluate_rlp_error_checks_returned
end InitECandidate.Runtime
