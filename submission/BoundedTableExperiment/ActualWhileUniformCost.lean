import ActualWhileCount

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The fixed loop-head events of one iteration. -/
def whileHeadEvents (fn : MlS) : List WorkEvent :=
  [.statement, .cost (whileOverhead + loopMoves fn)]

/-- Uniform N-iteration cost bound.  If every actual iteration (head + guard +
body) costs at most `perIter`, every terminal guard costs at most `terminal`,
and every guard-only failure costs at most `terminal`, then the whole actual
loop trace costs at most `n * perIter + terminal`.  This is independent of the
iteration index, so the same per-operation cost applies to all N iterations. -/
theorem whileCount_score_uniform {F : Type} {fn : MlS} {condition : ExpHOL 64}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    (count : WhileCount fn condition body s r post events n)
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
    coeff.score (executionWork events) ≤ n * perIter + terminal := by
  induction count with
  | stop guard =>
      have hs := hstop _ _ _ guard
      simp only [whileHeadEvents, executionWork, executionWork_append, Work.score_plus,
        List.cons_append, List.nil_append, List.append_assoc] at hs ⊢
      omega
  | next guard nonzero clock one rest ih =>
      have hi := hiter _ _ _ _ _ _ _ guard one
      simp only [whileHeadEvents, executionWork, executionWork_append, Work.score_plus,
        List.cons_append, List.nil_append, List.append_assoc,
        Nat.add_mul, Nat.one_mul] at hi ih ⊢
      omega
  | breakLoop guard nonzero one =>
      have hi := hiter _ _ _ _ _ _ _ guard one
      simp only [whileHeadEvents, executionWork, executionWork_append, Work.score_plus,
        List.cons_append, List.nil_append, List.append_assoc,
        Nat.add_mul, Nat.one_mul] at hi ⊢
      omega
  | continueLoop guard nonzero clock one rest ih =>
      have hi := hiter _ _ _ _ _ _ _ guard one
      simp only [whileHeadEvents, executionWork, executionWork_append, Work.score_plus,
        List.cons_append, List.nil_append, List.append_assoc,
        Nat.add_mul, Nat.one_mul] at hi ih ⊢
      omega
  | timeout guard nonzero clock =>
      have hs := hstop _ _ _ guard
      simp only [whileHeadEvents, executionWork, executionWork_append, Work.score_plus,
        List.cons_append, List.nil_append, List.append_assoc,
        Nat.add_mul, Nat.one_mul] at hs ⊢
      omega
  | missingGuard guard =>
      have hm := hmissing _ _ _ guard
      simp only [whileHeadEvents, executionWork, executionWork_append, Work.score_plus,
        List.cons_append, List.nil_append, List.append_assoc,
        Nat.add_mul, Nat.one_mul] at hm ⊢
      omega
  | invalidGuard guard notWord =>
      have hm := hmissing _ _ _ guard
      simp only [whileHeadEvents, executionWork, executionWork_append, Work.score_plus,
        List.cons_append, List.nil_append, List.append_assoc,
        Nat.add_mul, Nat.one_mul] at hm ⊢
      omega
  | propagate guard nonzero clock notBreak notContinue one =>
      have hi := hiter _ _ _ _ _ _ _ guard one
      simp only [whileHeadEvents, executionWork, executionWork_append, Work.score_plus,
        List.cons_append, List.nil_append, List.append_assoc,
        Nat.add_mul, Nat.one_mul] at hi ⊢
      omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.whileCount_score_uniform
