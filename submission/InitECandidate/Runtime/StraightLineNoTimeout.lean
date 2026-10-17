import InitECandidate.Runtime.SourceClock
import InitECandidate.Runtime.StoreControlFrame
import InitECandidate.Runtime.TrapNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Call-free and loop-free source code cannot consume fuel or produce timeout,
even if an expression, store, assignment, or exception check fails. -/
theorem evaluate_straightLine_no_timeout {F : Type} (program : ProgHOL 64)
    (supported : straightLine program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ some .timeOut := by
  cases shape : program with
  | skip => simp [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : straightLine body = true := by simpa only [shape,straightLine] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_straightLine_no_timeout body child _
      · simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | store destination value =>
    rcases (evaluate_store_control_frame state destination value).1 with normal | error
    · rw [normal]; simp
    · rw [error]; simp
  | seq first second =>
    have children : straightLine first = true ∧ straightLine second = true := by
      simpa only [shape,straightLine,Bool.and_eq_true] using supported
    exact evaluate_sequence_no_timeout state first second (evaluate_straightLine_no_timeout first children.1 state)
      (fun next => evaluate_straightLine_no_timeout second children.2 next)
  | ite condition yes no =>
    have children : straightLine yes = true ∧ straightLine no = true := by
      simpa only [shape,straightLine,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_straightLine_no_timeout no children.2 state
      · exact evaluate_straightLine_no_timeout yes children.1 state
    · simp
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value => exact evaluate_raise_no_timeout state name value
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | _ => simp [shape,straightLine] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega

#print axioms evaluate_straightLine_no_timeout
end InitECandidate.Runtime
