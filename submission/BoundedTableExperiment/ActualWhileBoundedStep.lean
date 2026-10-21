import ActualWhileCount

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

set_option maxHeartbeats 1000000

/-- A rank that strictly increases on every *continuing* body run (result
`none`) bounds the iteration count by 480.  Error/break body runs end the loop,
so they impose no rank condition. -/
theorem whileCount_le_480_none {F : Type} {fn : MlS} {condition : ExpHOL 64}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {rank : PanSemStateFiniteExact 64 F → Nat}
    (count : WhileCount fn condition body s r post events n)
    (start : rank s < 480)
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t) body result middle bodyEvents →
        (result = none ∨ result = some .continue) →
        rank t < rank middle ∧ rank middle < 480) :
    n ≤ 480 := by
  have main : rank s + n ≤ 480 := by
    induction count with
    | stop guard => omega
    | next guard nonzero clock one rest ih =>
        have hs := (step _ _ _ _ one (Or.inl rfl)).1
        have hrest := ih (step _ _ _ _ one (Or.inl rfl)).2
        omega
    | breakLoop guard nonzero one => omega
    | continueLoop guard nonzero clock one rest ih =>
        have hs := (step _ _ _ _ one (Or.inr rfl)).1
        have hrest := ih (step _ _ _ _ one (Or.inr rfl)).2
        omega
    | timeout guard nonzero clock => omega
    | missingGuard guard => omega
    | invalidGuard guard notWord => omega
    | propagate guard nonzero clock notBreak notContinue one => omega
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.whileCount_le_480_none
