import InitECandidate.Runtime.PanStatementWork

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang

set_option maxHeartbeats 1000000

/-- The zero work vector costs nothing. -/
theorem Work_score_zero (coeff : Work) : coeff.score ({ } : Work) = 0 := by
  simp [Work.score]

/-- The empty trace carries no work. -/
theorem executionWork_nil_score (coeff : Work) :
    coeff.score (executionWork ([] : List WorkEvent)) = 0 := by
  simp [executionWork, Work.score]

/-- Exact work decomposition of a candidate loop-body store trace: the
statement unit, address trace, value trace, memory event and store overhead add
up independently. -/
theorem executionWork_store_events (coeff : Work) (addressEvents valueEvents : List WorkEvent) :
    coeff.score (executionWork
        (WorkEvent.statement ::
          (addressEvents ++ valueEvents ++
            [WorkEvent.memory 1, WorkEvent.cost (storeOverhead 1)]))) =
      coeff.score WorkEvent.statement.units +
        coeff.score (executionWork addressEvents) +
        coeff.score (executionWork valueEvents) +
        coeff.score (WorkEvent.memory 1).units +
        coeff.score (WorkEvent.cost (storeOverhead 1)).units := by
  simp only [executionWork_score_cons, executionWork_score_append, executionWork, executionWork_nil_score, Work_score_zero,
    List.append_nil, List.nil_append,
    Work.score_plus]
  omega

/-- Exact work decomposition of a candidate loop-body assignment trace. -/
theorem executionWork_assign_events (coeff : Work) (valueEvents : List WorkEvent) :
    coeff.score (executionWork
        (WorkEvent.statement :: (valueEvents ++ [WorkEvent.copy 1]))) =
      coeff.score WorkEvent.statement.units +
        coeff.score (executionWork valueEvents) +
        coeff.score (WorkEvent.copy 1).units := by
  simp only [executionWork_score_cons, executionWork_score_append, executionWork, executionWork_nil_score, Work_score_zero,
    List.append_nil, List.nil_append,
    Work.score_plus]
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.executionWork_store_events
#print axioms BoundedTableExperiment.executionWork_assign_events
