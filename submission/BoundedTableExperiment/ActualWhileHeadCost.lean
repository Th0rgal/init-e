import ActualWhileCount

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Uniform loop-head cost: the fixed statement and while-overhead events of
one iteration cost the same sum regardless of the rest of the trace. -/
theorem while_head_work (coeff : Work) (fn : MlS) (rest : List WorkEvent) :
    coeff.score (executionWork
        (WorkEvent.statement ::
          WorkEvent.cost (whileOverhead + loopMoves fn) :: rest)) =
      (coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.score (executionWork rest) := by
  simp only [executionWork, Work.score_plus]
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.while_head_work
