import InitECandidate.Runtime.SourceCostGlobalsState
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsInitCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

theorem globals_plan_done_code {F : Type} {s bodyPost post : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult result}
    (h : callCostPlan s info returnShape bodyResult bodyPost = .done result post) :
    post.code = bodyPost.code := by
  unfold callCostPlan at h
  repeat' split at h
  all_goals (cases h)
  all_goals first | rfl | (simp only [setKvarHOLFinite]; split <;> rfl)

theorem globals_plan_handler_code {F : Type} {s bodyPost entry : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult program}
    (h : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    entry.code = bodyPost.code := by
  unfold callCostPlan at h
  repeat' split at h
  all_goals (cases h)
  all_goals rfl

theorem globals_stopPlan_code {F : Type} (bodyResult : Option (PanSemResultExact 64))
    (bodyPost : PanSemStateFiniteExact 64 F) :
    (declareCallStopPlan bodyResult bodyPost).2.code = bodyPost.code := by
  unfold declareCallStopPlan
  split <;> rfl

theorem globals_ofExact_code {F : Type} {s : PanSemStateFiniteExact 64 F}
    (m : PanSemStateExact 64 F) (h : m.FiniteSupport) (same : m.code = s.toExact.code) :
    (ofExact m h).code = s.code := by
  rcases hc : s.code with ⟨lookup, support⟩
  simp only [ofExact]
  have : m.code = lookup := by rw [same]; simp [toExact, hc]
  subst this
  rfl

/-- Statement runs never change the code map. -/
theorem StatementRun.code_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {p r ev}
    (run : StatementRun fn s p r post ev) : post.code = s.code := by
  have preserved := SemInitSupport.eval_code s p
  rw [run.sound] at preserved
  exact preserved

#print axioms StatementRun.code_eq
end InitECandidate.Runtime.FineCost
