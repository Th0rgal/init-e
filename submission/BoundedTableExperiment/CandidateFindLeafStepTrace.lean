import CandidateFindLeafPush

set_option maxHeartbeats 1000000

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Splitting a successful run of `candidateFindLeafStep` into its guard and
walk parts. -/
theorem candidateFindLeafStep_run_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafStep none post events) :
    ∃ (mid : PanSemStateFiniteExact 64 F)
      (guardEvents walkEvents : List WorkEvent),
      events = guardEvents ++ walkEvents ∧
      StatementRun fn s candidateFindLeafGuard none mid guardEvents ∧
      StatementRun fn mid candidateFindLeafWalk none post walkEvents := by
  rw [show candidateFindLeafStep =
    .seq candidateFindLeafGuard candidateFindLeafWalk from rfl] at run
  cases run with
  | seqNext one two => exact ⟨_, _, _, rfl, one, two⟩
  | seqStop terminal _ => exact absurd rfl terminal

/-- Splitting a successful run of `candidateFindLeafWalk` into push, depth
bump, and route/child selection. -/
theorem candidateFindLeafWalk_run_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafWalk none post events) :
    ∃ (afterPush afterBump : PanSemStateFiniteExact 64 F)
      (pushEvents bumpEvents routeEvents : List WorkEvent),
      events = pushEvents ++ (bumpEvents ++ routeEvents) ∧
      StatementRun fn s candidateFindLeafPush none afterPush pushEvents ∧
      StatementRun fn afterPush candidateFindLeafBump none afterBump bumpEvents ∧
      StatementRun fn afterBump candidateFindLeafRoute none post routeEvents := by
  change StatementRun fn s
    (.seq candidateFindLeafPush (.seq candidateFindLeafBump candidateFindLeafRoute))
    none post events at run
  cases run with
  | seqNext one two =>
      cases two with
      | seqNext bumpRun routeRun =>
          exact ⟨_, _, _, _, _, rfl, one, bumpRun, routeRun⟩
      | seqStop terminal _ => exact absurd rfl terminal
  | seqStop terminal _ => exact absurd rfl terminal

/-- Full one-iteration trace of the search loop: guard events, path push,
depth bump, and route/child selection, in order. -/
theorem candidateFindLeafStep_trace {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafStep none post events) :
    ∃ (afterGuard afterPush afterBump : PanSemStateFiniteExact 64 F)
      (guardEvents pushEvents bumpEvents routeEvents : List WorkEvent),
      events = guardEvents ++ (pushEvents ++ (bumpEvents ++ routeEvents)) ∧
      StatementRun fn s candidateFindLeafGuard none afterGuard guardEvents ∧
      StatementRun fn afterGuard candidateFindLeafPush none afterPush pushEvents ∧
      StatementRun fn afterPush candidateFindLeafBump none afterBump bumpEvents ∧
      StatementRun fn afterBump candidateFindLeafRoute none post routeEvents := by
  obtain ⟨mid, guardEvents, walkEvents, rfl, guardRun, walkRun⟩ :=
    candidateFindLeafStep_run_split run
  obtain ⟨afterPush, afterBump, pushEvents, bumpEvents, routeEvents,
    rfl, pushRun, bumpRun, routeRun⟩ := candidateFindLeafWalk_run_split walkRun
  exact ⟨mid, afterPush, afterBump, guardEvents, pushEvents, bumpEvents,
    routeEvents, rfl, guardRun, pushRun, bumpRun, routeRun⟩

/-- Actual score of the full one-iteration trace is the sum of its four parts. -/
theorem candidateFindLeafStep_trace_score {F : Type} {fn : MlS} (coeff : Work)
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafStep none post events) :
    ∃ (guardEvents pushEvents bumpEvents routeEvents : List WorkEvent),
      events = guardEvents ++ (pushEvents ++ (bumpEvents ++ routeEvents)) ∧
      coeff.score (executionWork events) =
        coeff.score (executionWork guardEvents) +
        coeff.score (executionWork pushEvents) +
        coeff.score (executionWork bumpEvents) +
        coeff.score (executionWork routeEvents) := by
  obtain ⟨_, _, _, guardEvents, pushEvents, bumpEvents, routeEvents,
    rfl, _, _, _, _⟩ := candidateFindLeafStep_trace run
  refine ⟨guardEvents, pushEvents, bumpEvents, routeEvents, rfl, ?_⟩
  rw [executionWork_score_append, executionWork_score_append,
    executionWork_score_append]
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateFindLeafStep_run_split
#print axioms BoundedTableExperiment.candidateFindLeafWalk_run_split
#print axioms BoundedTableExperiment.candidateFindLeafStep_trace
#print axioms BoundedTableExperiment.candidateFindLeafStep_trace_score
