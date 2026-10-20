import InitECandidate.Runtime.SourceCostGlobalsState
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

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
    (run : StatementRun s p r post ev) : post.code = s.code := by
  induction run
  case sharedLoad run =>
    simp at run
    obtain ⟨_, rfl⟩ := run
    apply globals_ofExact_code
    unfold shMemLoadClauseHOLFiniteExact shMemLoadClauseHOLExact
    split
    all_goals
      simp only []
      split
      all_goals first | rfl | (unfold shMemLoadHOLExact; repeat' split) <;>
        first | rfl | (simp only [setKvarHOLExact]; split <;> rfl)
  case sharedStore run =>
    rw [evaluateHOLFiniteState_shMemStore_total] at run
    simp only [] at run
    split at run
    · obtain ⟨_, rfl⟩ := Prod.mk.inj run
      apply globals_ofExact_code
      unfold shMemStoreHOLExact
      repeat' split
      all_goals rfl
    · obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl
  case external run =>
    rw [evaluateHOLFiniteState_extCall_source] at run
    repeat' split at run
    all_goals
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      first | rfl | (apply globals_ofExact_code; rfl)
  case callDone plan ih =>
    rw [globals_plan_done_code plan, ih]; rfl
  case callHandler plan _ ihBody ihHandler =>
    rw [ihHandler, globals_plan_handler_code plan, ihBody]; rfl
  case declareCallStopped ih =>
    rw [globals_stopPlan_code, ih]; rfl
  all_goals first
    | rfl
    | assumption
    | (simp only [setKvarHOLFinite]; split <;> rfl)
    | (simp_all [setVarHOLFinite, callEntryStateHOLFinite, decClockHOLFinite]; done)
    | (simp_all; rfl)

#print axioms StatementRun.code_eq
end InitECandidate.Runtime.FineCost
