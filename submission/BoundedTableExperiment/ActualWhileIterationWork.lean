import ActualWhileHeadCost

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang

set_option maxHeartbeats 1000000

/-- Work of one actual iteration: the loop head, guard and body decompose
additively into the fixed head score plus the guard trace score plus the body
trace score. -/
theorem executionWork_head_guard_body (coeff : Work) (fn : MlS)
    (guardEvents bodyEvents : List WorkEvent) :
    coeff.score (executionWork
        (WorkEvent.statement ::
          WorkEvent.cost (whileOverhead + loopMoves fn) ::
            (guardEvents ++ bodyEvents))) =
      (coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        (coeff.score (executionWork guardEvents) +
          coeff.score (executionWork bodyEvents)) := by
  rw [while_head_work, executionWork_score_append]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.executionWork_head_guard_body
