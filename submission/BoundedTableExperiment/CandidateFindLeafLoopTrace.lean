import CandidateFindLeafStepTrace

set_option maxHeartbeats 1000000

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One unfolding of an actual successful search-loop run: it either stops with
a false guard, continues with one body iteration and a rest run, or exits via
`break`. -/
theorem candidateFindLeafLoop_run_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafLoop none post events) :
    (∃ guardEvents : List WorkEvent,
      events = .statement :: .cost (whileOverhead + loopMoves fn) :: guardEvents ∧
      CostedExpressionRun s
        (.cmp .notEqual (.var .local (ofString "node")) (.const (BitVec.ofNat 64 0)))
        (some (.val (.word 0))) guardEvents) ∨
    (∃ (value : BitVec 64) (middle : PanSemStateFiniteExact 64 F)
        (guardEvents bodyEvents restEvents : List WorkEvent),
      value ≠ 0 ∧
      events = .statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents ++ restEvents) ∧
      CostedExpressionRun s
        (.cmp .notEqual (.var .local (ofString "node")) (.const (BitVec.ofNat 64 0)))
        (some (.val (.word value))) guardEvents ∧
      StatementRun fn (decClockHOLFinite s) candidateFindLeafStep none middle bodyEvents ∧
      StatementRun fn middle candidateFindLeafLoop none post restEvents) ∨
    (∃ (value : BitVec 64) (post' : PanSemStateFiniteExact 64 F)
        (guardEvents bodyEvents : List WorkEvent),
      value ≠ 0 ∧
      events = .statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents) ∧
      CostedExpressionRun s
        (.cmp .notEqual (.var .local (ofString "node")) (.const (BitVec.ofNat 64 0)))
        (some (.val (.word value))) guardEvents ∧
      StatementRun fn (decClockHOLFinite s) candidateFindLeafStep
        (some .break) post' bodyEvents) ∨
    (∃ (value : BitVec 64) (middle : PanSemStateFiniteExact 64 F)
        (guardEvents bodyEvents restEvents : List WorkEvent),
      value ≠ 0 ∧
      events = .statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents ++ restEvents) ∧
      CostedExpressionRun s
        (.cmp .notEqual (.var .local (ofString "node")) (.const (BitVec.ofNat 64 0)))
        (some (.val (.word value))) guardEvents ∧
      StatementRun fn (decClockHOLFinite s) candidateFindLeafStep
        (some .continue) middle bodyEvents ∧
      StatementRun fn middle candidateFindLeafLoop none post restEvents) := by
  change StatementRun fn s
    (.while (.cmp .notEqual (.var .local (ofString "node")) (.const (BitVec.ofNat 64 0)))
      candidateFindLeafStep)
    none post events at run
  cases run with
  | whileFalse guard => exact Or.inl ⟨_, rfl, guard⟩
  | whileNext guard nonzero clock one rest =>
      exact Or.inr (Or.inl ⟨_, _, _, _, _, nonzero, rfl, guard, one, rest⟩)
  | whileBreak guard nonzero clock one =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, nonzero, rfl, guard, one⟩))
  | whileContinue guard nonzero clock one rest =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, nonzero, rfl, guard, one, rest⟩))

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateFindLeafLoop_run_split
