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
