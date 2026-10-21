import CandidateHtabSetLinkTrace

set_option maxHeartbeats 1000000

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One iteration of the binary-search loop. -/
def candidateHtabSetBsearchStep : ProgHOL 64 :=
  .dec (ofString "mid") .one (.shift .asr (.op .add [loc "lo",loc "hi"]) (.const 1))
    (.dec (ofString "mr") .one (lw candidateHtabSetMrAddr)
      (.ite (.cmp .lower (loc "d") (loc "mr"))
        (.assign .local (ofString "hi") (loc "mid"))
        (.assign .local (ofString "lo") (.op .add [loc "mid",.const 1]))))

theorem candidateHtabSetBsearch_eq :
    candidateHtabSetBsearch =
      .while (.cmp .less (loc "lo") (loc "hi")) candidateHtabSetBsearchStep := rfl

/-- Any actual successful binary-search run stops, iterates, breaks, or
continues, with the actual guard/body/rest runs. -/
theorem candidateHtabSetBsearch_run_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateHtabSetBsearch none post events) :
    (∃ guardEvents : List WorkEvent,
      events = .statement :: .cost (whileOverhead + loopMoves fn) :: guardEvents ∧
      CostedExpressionRun s (.cmp .less (loc "lo") (loc "hi"))
        (some (.val (.word 0))) guardEvents) ∨
    (∃ (value : BitVec 64) (middle : PanSemStateFiniteExact 64 F)
        (guardEvents bodyEvents restEvents : List WorkEvent),
      value ≠ 0 ∧
      events = .statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents ++ restEvents) ∧
      CostedExpressionRun s (.cmp .less (loc "lo") (loc "hi"))
        (some (.val (.word value))) guardEvents ∧
      StatementRun fn (decClockHOLFinite s) candidateHtabSetBsearchStep
        none middle bodyEvents ∧
      StatementRun fn middle candidateHtabSetBsearch none post restEvents) ∨
    (∃ (value : BitVec 64) (post' : PanSemStateFiniteExact 64 F)
        (guardEvents bodyEvents : List WorkEvent),
      value ≠ 0 ∧
      events = .statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents) ∧
      CostedExpressionRun s (.cmp .less (loc "lo") (loc "hi"))
        (some (.val (.word value))) guardEvents ∧
      StatementRun fn (decClockHOLFinite s) candidateHtabSetBsearchStep
        (some .break) post' bodyEvents) ∨
    (∃ (value : BitVec 64) (middle : PanSemStateFiniteExact 64 F)
        (guardEvents bodyEvents restEvents : List WorkEvent),
      value ≠ 0 ∧
      events = .statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents ++ restEvents) ∧
      CostedExpressionRun s (.cmp .less (loc "lo") (loc "hi"))
        (some (.val (.word value))) guardEvents ∧
      StatementRun fn (decClockHOLFinite s) candidateHtabSetBsearchStep
        (some .continue) middle bodyEvents ∧
      StatementRun fn middle candidateHtabSetBsearch none post restEvents) := by
  rw [candidateHtabSetBsearch_eq] at run
  cases run with
  | whileFalse guard => exact Or.inl ⟨_, rfl, guard⟩
  | whileNext guard nonzero clock one rest =>
      exact Or.inr (Or.inl ⟨_, _, _, _, _, nonzero, rfl, guard, one, rest⟩)
  | whileBreak guard nonzero clock one =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, nonzero, rfl, guard, one⟩))
  | whileContinue guard nonzero clock one rest =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, nonzero, rfl, guard, one, rest⟩))

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateHtabSetBsearch_run_split
