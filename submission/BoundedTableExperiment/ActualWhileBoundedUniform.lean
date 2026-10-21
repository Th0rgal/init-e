import ActualWhileRouteBound
import ActualWhileUniformCost

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Actual finite loop bound together with uniform per-operation cost:
every actual candidate loop has at most 480 iterations and its whole event
trace costs at most `480 * perIter + terminal`, with the same per-iteration
cost bound for every iteration. -/
theorem whileCount_bounded_uniform {F : Type} {fn : MlS} {condition : ExpHOL 64}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {rank : PanSemStateFiniteExact 64 F → Nat}
    (count : WhileCount fn condition body s r post events n)
    (start : rank s < 480)
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t) body result middle bodyEvents →
        rank t < rank middle ∧ rank middle < 480)
    (coeff : Work) (perIter terminal : Nat)
    (hiter : ∀ (t u v : PanSemStateFiniteExact 64 F) (value : Option (ValueHOL 64))
      (result : Option (PanSemResultExact 64))
      (guardEvents bodyEvents : List WorkEvent),
      CostedExpressionRun t condition value guardEvents →
      StatementRun fn v body result u bodyEvents →
        coeff.score (executionWork
          (whileHeadEvents fn ++ (guardEvents ++ bodyEvents))) ≤ perIter)
    (hstop : ∀ (t : PanSemStateFiniteExact 64 F) (value : Option (ValueHOL 64))
      (guardEvents : List WorkEvent),
      CostedExpressionRun t condition value guardEvents →
        coeff.score (executionWork (whileHeadEvents fn ++ guardEvents)) ≤ terminal)
    (hmissing : ∀ (t : PanSemStateFiniteExact 64 F) (value : Option (ValueHOL 64))
      (guardEvents : List WorkEvent),
      CostedExpressionRun t condition value guardEvents →
        coeff.score (executionWork
          (WorkEvent.statement :: guardEvents)) ≤ terminal) :
    n ≤ 480 ∧ coeff.score (executionWork events) ≤ 480 * perIter + terminal := by
  refine ⟨whileCount_le_480 count start step, ?_⟩
  have hcost := whileCount_score_uniform count coeff perIter terminal hiter hstop hmissing
  have hn := whileCount_le_480 count start step
  have hmono : n * perIter ≤ 480 * perIter := Nat.mul_le_mul_right perIter hn
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.whileCount_bounded_uniform
