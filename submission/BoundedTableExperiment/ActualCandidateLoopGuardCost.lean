import ActualWhileRouteBound
import ActualWhileIterationWork
import ActualWhileUniformCost
import InitECandidate.Runtime.PanSourcePriceDef

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- The actual candidate loop guard `i < cap` costs 98 source units when both
locals are one-word values. -/
theorem sourcePrice_loop_guard {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : valueInfo s.locals (ofString "i") = some (ShapeHOL.one, 1))
    (hc : valueInfo s.locals (ofString "cap") = some (ShapeHOL.one, 1)) :
    sourcePrice s (.cmp .lower (.var .local (ofString "i"))
      (.var .local (ofString "cap"))) = 98 := by
  simp [sourcePrice, sourcePrices, exprPrices, hi, hc]

/-- Any actual guard trace of `i < cap` at one-word locals costs at most
`coeff.nativeCost * 98`. -/
theorem loop_guard_score_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {value : Option (ValueHOL 64)} {events : List WorkEvent} (coeff : Work)
    (run : CostedExpressionRun s
      (.cmp .lower (.var .local (ofString "i"))
        (.var .local (ofString "cap"))) value events)
    (hi : valueInfo s.locals (ofString "i") = some (ShapeHOL.one, 1))
    (hc : valueInfo s.locals (ofString "cap") = some (ShapeHOL.one, 1)) :
    coeff.score (executionWork events) ≤ coeff.nativeCost * 98 := by
  rw [run.events_eq]
  change expressionCost coeff s
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap"))) ≤
      coeff.nativeCost * 98
  rw [expressionCost_eq, sourcePrice_loop_guard s hi hc]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.sourcePrice_loop_guard
#print axioms BoundedTableExperiment.loop_guard_score_bound

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform cost for the actual candidate loop guard `i < cap` with the
concrete price 98, stated without a separate head-score symbol: every
iteration costs at most the literal loop-head work plus `nativeCost * 98` plus
the body bound. -/
theorem candidate_loop_uniform_cost_literal {F : Type} {fn : MlS}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    (count : WhileCount fn
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
      body s r post events n)
    (coeff : Work) (bodyScore terminal : Nat)
    (hshape : ∀ (t : PanSemStateFiniteExact 64 F)
      (value : Option (ValueHOL 64)) (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      valueInfo t.locals (ofString "i") = some (ShapeHOL.one, 1) ∧
        valueInfo t.locals (ofString "cap") = some (ShapeHOL.one, 1))
    (hbody : ∀ (t u v : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn v body result u bodyEvents →
        coeff.score (executionWork bodyEvents) ≤ bodyScore)
    (hmissing : ∀ (t : PanSemStateFiniteExact 64 F)
      (value : Option (ValueHOL 64)) (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      coeff.score (executionWork
        (WorkEvent.statement :: guardEvents)) ≤ terminal)
    (hterminal : (coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98 ≤ terminal) :
    coeff.score (executionWork events) ≤
      n * ((coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98 + bodyScore) + terminal := by
  refine whileCount_score_uniform count coeff
    ((coeff.score WorkEvent.statement.units +
      coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
      coeff.nativeCost * 98 + bodyScore) terminal ?_ ?_ hmissing
  · intro t u v value result guardEvents bodyEvents rung one
    have hg := loop_guard_score_bound coeff rung
      (hshape t value guardEvents rung).1 (hshape t value guardEvents rung).2
    have hb := hbody t u v result bodyEvents one
    rw [rung.events_eq] at hg ⊢
    simp only [whileHeadEvents, List.cons_append, List.nil_append]
    rw [executionWork_head_guard_body]
    omega
  · intro t value guardEvents rung
    have hg := loop_guard_score_bound coeff rung
      (hshape t value guardEvents rung).1 (hshape t value guardEvents rung).2
    rw [rung.events_eq] at hg ⊢
    simp only [whileHeadEvents, List.cons_append, List.nil_append]
    rw [while_head_work]
    omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_loop_uniform_cost_literal

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Candidate loop `i < cap`: at most 480 iterations, and total work at most
`480 * (head + nativeCost * 98 + bodyScore) + terminal`. -/
theorem candidate_loop_bounded_uniform_cost_literal {F : Type} {fn : MlS}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {rank : PanSemStateFiniteExact 64 F → Nat}
    (count : WhileCount fn
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
      body s r post events n)
    (start : rank s < 480)
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t) body result middle bodyEvents →
        rank t < rank middle ∧ rank middle < 480)
    (coeff : Work) (bodyScore terminal : Nat)
    (hshape : ∀ (t : PanSemStateFiniteExact 64 F)
      (value : Option (ValueHOL 64)) (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      valueInfo t.locals (ofString "i") = some (ShapeHOL.one, 1) ∧
        valueInfo t.locals (ofString "cap") = some (ShapeHOL.one, 1))
    (hbody : ∀ (t u v : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn v body result u bodyEvents →
        coeff.score (executionWork bodyEvents) ≤ bodyScore)
    (hmissing : ∀ (t : PanSemStateFiniteExact 64 F)
      (value : Option (ValueHOL 64)) (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      coeff.score (executionWork
        (WorkEvent.statement :: guardEvents)) ≤ terminal)
    (hterminal : (coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98 ≤ terminal) :
    n ≤ 480 ∧ coeff.score (executionWork events) ≤
      480 * (((coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98) + bodyScore) + terminal := by
  refine ⟨whileCount_le_480 count start step, ?_⟩
  have hcost := candidate_loop_uniform_cost_literal count coeff bodyScore terminal
    hshape hbody hmissing hterminal
  have hn := whileCount_le_480 count start step
  have hmono : n * (((coeff.score WorkEvent.statement.units +
      coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
      coeff.nativeCost * 98) + bodyScore) ≤
      480 * (((coeff.score WorkEvent.statement.units +
      coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
      coeff.nativeCost * 98) + bodyScore) := Nat.mul_le_mul_right _ hn
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_loop_bounded_uniform_cost_literal

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Candidate loop `i < cap` with self-terminated cost: at most 480 iterations,
and total work at most `480 * (head + nativeCost*98 + bodyScore)` plus the
terminal budget `statement + head + nativeCost*98`.  No separate terminal or
missing-guard hypotheses are needed. -/
theorem candidate_loop_selfterminated_cost {F : Type} {fn : MlS}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {rank : PanSemStateFiniteExact 64 F → Nat}
    (count : WhileCount fn
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
      body s r post events n)
    (start : rank s < 480)
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t) body result middle bodyEvents →
        rank t < rank middle ∧ rank middle < 480)
    (coeff : Work) (bodyScore : Nat)
    (hshape : ∀ (t : PanSemStateFiniteExact 64 F)
      (value : Option (ValueHOL 64)) (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      valueInfo t.locals (ofString "i") = some (ShapeHOL.one, 1) ∧
        valueInfo t.locals (ofString "cap") = some (ShapeHOL.one, 1))
    (hbody : ∀ (t u v : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn v body result u bodyEvents →
        coeff.score (executionWork bodyEvents) ≤ bodyScore) :
    n ≤ 480 ∧ coeff.score (executionWork events) ≤
      480 * (((coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98) + bodyScore) +
        (coeff.score WorkEvent.statement.units +
          ((coeff.score WorkEvent.statement.units +
            coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
            coeff.nativeCost * 98)) := by
  refine candidate_loop_bounded_uniform_cost_literal count start step coeff bodyScore
    (coeff.score WorkEvent.statement.units +
      ((coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98)) hshape hbody ?_ ?_
  · intro t value guardEvents rung
    have hg := loop_guard_score_bound coeff rung
      (hshape t value guardEvents rung).1 (hshape t value guardEvents rung).2
    rw [rung.events_eq] at hg ⊢
    rw [executionWork_score_cons]
    omega
  · omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_loop_selfterminated_cost
