import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Source sequence reassociation preserves both evaluation result and state,
including every interrupting result. -/
theorem evaluate_seq_assoc {width : Nat} [NeZero width] {F : Type}
    (state : PanSemStateFiniteExact width F) (first second third : ProgHOL width) :
    evaluateHOLFiniteState state (.seq (.seq first second) third) =
      evaluateHOLFiniteState state (.seq first (.seq second third)) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  cases firstRun : evaluateHOLFiniteState state first with
  | mk result middle =>
    cases result with
    | some result => rfl
    | none =>
      cases secondRun : evaluateHOLFiniteState middle second with
      | mk result post => cases result <;> rfl

#print axioms evaluate_seq_assoc
end InitECandidate.Runtime
