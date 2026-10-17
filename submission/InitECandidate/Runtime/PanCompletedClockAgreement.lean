import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Completed non-timeout evaluations from the same state cannot disagree
about their result merely because the initial clocks differ. -/
theorem evaluate_completed_clock_agreement {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) (firstClock secondClock : Nat)
    (firstResult secondResult : Option (PanSemResultExact 64))
    (firstPost secondPost : PanSemStateFiniteExact 64 F)
    (firstRun : evaluateHOLFiniteState {state with clock := firstClock} program = (firstResult,firstPost))
    (secondRun : evaluateHOLFiniteState {state with clock := secondClock} program = (secondResult,secondPost))
    (firstDone : firstResult ≠ some .timeOut) (secondDone : secondResult ≠ some .timeOut) :
    firstResult = secondResult := by
  have first := panPropsEvaluateAddClockEq program {state with clock := firstClock} firstResult firstPost secondClock ⟨firstRun,firstDone⟩
  have second := panPropsEvaluateAddClockEq program {state with clock := secondClock} secondResult secondPost firstClock ⟨secondRun,secondDone⟩
  change evaluateHOLFiniteState {state with clock := firstClock + secondClock} program = _ at first
  change evaluateHOLFiniteState {state with clock := secondClock + firstClock} program = _ at second
  rw [Nat.add_comm secondClock firstClock] at second
  exact (Prod.mk.inj (first.symm.trans second)).1

/-- In particular the decoded word returned by a reader is clock-independent
once both runs have returned successfully. -/
theorem evaluate_returned_clock_agreement {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) (firstClock secondClock : Nat) (firstValue secondValue : ValueHOL 64)
    (firstPost secondPost : PanSemStateFiniteExact 64 F)
    (firstRun : evaluateHOLFiniteState {state with clock := firstClock} program = (some (.returned firstValue),firstPost))
    (secondRun : evaluateHOLFiniteState {state with clock := secondClock} program = (some (.returned secondValue),secondPost)) :
    firstValue = secondValue := by
  have equal := evaluate_completed_clock_agreement state program firstClock secondClock _ _ firstPost secondPost
    firstRun secondRun (by simp) (by simp)
  exact PanSemResultExact.returned.inj (Option.some.inj equal)

#print axioms evaluate_completed_clock_agreement
#print axioms evaluate_returned_clock_agreement
end InitECandidate.Runtime
