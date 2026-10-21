import ActualWhileCount

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 1000000

/-- A rank strictly increasing on every actual loop-body run bounds the number
of loop iterations by 480.  Instantiate `rank` with the decoded route of the
current node and derive the step from the live-edge trie. -/
theorem whileCount_rank_le_480 {F : Type} {fn : MlS} {condition : ExpHOL 64}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {rank : PanSemStateFiniteExact 64 F → Nat}
    (count : WhileCount fn condition body s r post events n)
    (start : rank s < 480)
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t) body result middle bodyEvents →
        rank t < rank middle ∧ rank middle < 480) :
    rank s + n ≤ 480 := by
  induction count with
  | stop guard => omega
  | next guard nonzero clock one rest ih =>
      have hs := (step _ _ _ _ one).1
      have hrest := ih (step _ _ _ _ one).2
      omega
  | breakLoop guard nonzero one =>
      have hs := (step _ _ _ _ one).1
      omega
  | continueLoop guard nonzero clock one rest ih =>
      have hs := (step _ _ _ _ one).1
      have hrest := ih (step _ _ _ _ one).2
      omega
  | timeout guard nonzero clock => omega
  | missingGuard guard => omega
  | invalidGuard guard notWord => omega
  | propagate guard nonzero clock notBreak notContinue one =>
      have hs := (step _ _ _ _ one).1
      omega

/-- Consequently the actual loop count itself is at most 480. -/
theorem whileCount_le_480 {F : Type} {fn : MlS} {condition : ExpHOL 64}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {rank : PanSemStateFiniteExact 64 F → Nat}
    (count : WhileCount fn condition body s r post events n)
    (start : rank s < 480)
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t) body result middle bodyEvents →
        rank t < rank middle ∧ rank middle < 480) :
    n ≤ 480 := by
  have h := whileCount_rank_le_480 count start step
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.whileCount_rank_le_480
#print axioms BoundedTableExperiment.whileCount_le_480
