import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Local calculations without explicit control transfers. -/
def straightLocalOnly : ProgHOL 64 → Bool
  | .dec _ _ _ body => straightLocalOnly body
  | .seq first second => straightLocalOnly first && straightLocalOnly second
  | .ite _ yes no => straightLocalOnly yes && straightLocalOnly no
  | .assign .local _ _ | .skip => true
  | _ => false

theorem evaluate_straightLocal_outcomes {F : Type} (program : ProgHOL 64)
    (supported : straightLocalOnly program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 = none ∨
      (evaluateHOLFiniteState state program).1 = some .error := by
  cases shape : program with
  | skip => left; rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : straightLocalOnly body = true := by simpa only [shape,straightLocalOnly] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · right; rfl
    · split
      · exact evaluate_straightLocal_outcomes body child _
      · right; rfl
  | assign kind name value =>
    cases kind with
    | global => simp [shape,straightLocalOnly] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · right; rfl
      · split
        · left; rfl
        · right; rfl
  | seq first second =>
    have children : straightLocalOnly first = true ∧ straightLocalOnly second = true := by
      simpa only [shape,straightLocalOnly,Bool.and_eq_true] using supported
    have outcomes := evaluate_straightLocal_outcomes first children.1 state
    rw [evaluateHOLFiniteState_seq_line780]
    cases ran : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [ran] at outcomes
      rcases outcomes with normal | error
      · change result = none at normal
        subst result
        exact evaluate_straightLocal_outcomes second children.2 middle
      · change result = some .error at error
        subst result
        right; rfl
  | ite condition yes no =>
    have children : straightLocalOnly yes = true ∧ straightLocalOnly no = true := by
      simpa only [shape,straightLocalOnly,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_straightLocal_outcomes no children.2 state
      · exact evaluate_straightLocal_outcomes yes children.1 state
    · right; rfl
  | _ => simp [shape,straightLocalOnly] at supported
termination_by sizeOf program

#print axioms evaluate_straightLocal_outcomes
end InitECandidate.Runtime
