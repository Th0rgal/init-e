import InitECandidate.Runtime.TrapNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Pure checks may branch or raise; every normal outcome retains the full state. -/
def guardOnly : ProgHOL 64 → Bool
  | .skip | .raise _ _ => true
  | .ite _ yes no => guardOnly yes && guardOnly no
  | .seq first second => guardOnly first && guardOnly second
  | _ => false

theorem evaluate_guard_only_flow {F : Type} (p : ProgHOL 64) (supported : guardOnly p = true)
    (s : PanSemStateFiniteExact 64 F) :
    ((evaluateHOLFiniteState s p).1 = none → (evaluateHOLFiniteState s p).2 = s) ∧
    (∀ v, (evaluateHOLFiniteState s p).1 ≠ some (.returned v)) := by
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip]
  | raise name value =>
    refine ⟨?_,fun v => evaluate_raise_no_return s name value v⟩
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | ite condition yes no =>
    have pieces : guardOnly yes = true ∧ guardOnly no = true := by
      simpa only [shape,guardOnly,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_guard_only_flow no pieces.2 s
      · exact evaluate_guard_only_flow yes pieces.1 s
    · simp
  | seq first second =>
    have pieces : guardOnly first = true ∧ guardOnly second = true := by
      simpa only [shape,guardOnly,Bool.and_eq_true] using supported
    have firstFlow := evaluate_guard_only_flow first pieces.1 s
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState s first with
    | mk result middle =>
      rw [firstRun] at firstFlow
      cases result with
      | none =>
        have same : middle = s := firstFlow.1 rfl
        subst middle
        exact evaluate_guard_only_flow second pieces.2 s
      | some r => exact ⟨by simp,firstFlow.2⟩
  | _ => simp [shape,guardOnly] at supported
termination_by sizeOf p
decreasing_by all_goals simp_all <;> omega

/-- A return after pure checks must have executed the tail from the unchanged state. -/
theorem guard_only_seq_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (checks tail : ProgHOL 64) (supported : guardOnly checks = true) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (.seq checks tail) = (some (.returned v),post)) :
    evaluateHOLFiniteState s tail = (some (.returned v),post) := by
  have flow := evaluate_guard_only_flow checks supported s
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases checked : evaluateHOLFiniteState s checks with
  | mk result middle =>
    rw [checked] at run flow
    cases result with
    | none =>
      have same : middle = s := flow.1 rfl
      subst middle
      exact run
    | some r => exact False.elim (flow.2 v (Prod.mk.inj run).1)

#print axioms evaluate_guard_only_flow
#print axioms guard_only_seq_returned
end InitECandidate.Runtime
