import InitECandidate.Runtime.SourceCostGlobalsDomain
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! An exception result carries a value of its declared exception shape. -/

theorem StatementRun.eshapes_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {p r ev}
    (run : StatementRun s p r post ev) : post.eshapes = s.eshapes := by
  classical
  have h := evaluateInvariantsHOLFinite p (PanPropsEvalStateFiniteExact.ofPanSemFinite s) _ _ rfl
  have he := h.2.2.2.1
  simp only [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at he
  rw [run.sound] at he
  exact he

/-- Exception results carry declared shapes. -/
def ExnDeclared {F : Type} (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64)) : Prop :=
  ∀ eid value, r = some (.exception eid value) → s.eshapes.lookup eid = some (shapeOfHOLExact value)

theorem exn_plan_done {F : Type} {s bodyPost post : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult result}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post) :
    ∀ eid value, result = some (.exception eid value) → bodyResult = some (.exception eid value) := by
  intro eid value hr
  subst hr
  unfold callCostPlan at plan
  repeat' split at plan
  all_goals (cases plan)
  all_goals first | rfl | (rename_i h; first | (cases h; rfl) | skip)

theorem exn_plan_handler_eshapes {F : Type} {s bodyPost entry : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult program}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    entry.eshapes = bodyPost.eshapes := by
  unfold callCostPlan at plan
  repeat' split at plan
  all_goals (cases plan)
  all_goals rfl

theorem exn_stopPlan {F : Type} (bodyResult : Option (PanSemResultExact 64))
    (bodyPost : PanSemStateFiniteExact 64 F) :
    ∀ eid value, (declareCallStopPlan bodyResult bodyPost).1 = some (.exception eid value) →
      bodyResult = some (.exception eid value) := by
  intro eid value h
  unfold declareCallStopPlan at h
  split at h <;> simp_all

theorem StatementRun.exn_declared {F : Type} {s post : PanSemStateFiniteExact 64 F} {p r ev}
    (run : StatementRun s p r post ev) : ExnDeclared s r := by
  induction run
  case seqNext one _ _ ih2 =>
    intro eid v h; have := ih2 eid v h; rwa [one.eshapes_eq] at this
  case seqStop ih => exact ih
  case iteYes ih => exact ih
  case iteNo ih => exact ih
  case whileNext one _ _ ih2 =>
    intro eid v h; have := ih2 eid v h; rw [one.eshapes_eq] at this; exact this
  case whileContinue one _ _ ih2 =>
    intro eid v h; have := ih2 eid v h; rw [one.eshapes_eq] at this; exact this
  case whilePropagate ih => exact ih
  case declareValue ih => exact ih
  case raiseValue declared shapeMatches _ =>
    intro eid v h
    simp only [Option.some.injEq, PanSemResultExact.exception.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [declared, shapeMatches]
  case callDone plan ih =>
    intro eid v h
    exact ih eid v (exn_plan_done plan eid v h)
  case callHandler bodyRun plan _ _ ihHandler =>
    intro eid v h
    have := ihHandler eid v h
    rw [exn_plan_handler_eshapes plan, bodyRun.eshapes_eq] at this
    exact this
  case declareCallReturn bodyRun _ _ _ ihCont =>
    intro eid v h
    have := ihCont eid v h
    simp only [setVarHOLFinite] at this
    rw [bodyRun.eshapes_eq] at this
    exact this
  case declareCallStopped ih =>
    intro eid v h
    exact ih eid v (exn_stopPlan _ _ eid v h)
  case external run =>
    intro eid v h
    subst h
    rw [evaluateHOLFiniteState_extCall_source] at run
    repeat' split at run
    all_goals (have := (Prod.mk.inj run).1; cases this)
  case sharedStore run =>
    intro eid v h
    subst h
    rw [evaluateHOLFiniteState_shMemStore_total] at run
    simp only [] at run
    split at run
    · have h1 := (Prod.mk.inj run).1
      revert h1
      unfold shMemStoreHOLExact
      repeat' split
      all_goals simp
    · have := (Prod.mk.inj run).1; cases this
  case sharedLoad run =>
    intro eid v h
    subst h
    simp at run
    obtain ⟨h1, -⟩ := run
    revert h1
    unfold shMemLoadClauseHOLFiniteExact shMemLoadClauseHOLExact
    split
    all_goals
      simp only []
      split
      all_goals first | simp | (unfold shMemLoadHOLExact; repeat' split) <;> simp
  all_goals (intro eid v h; cases h)

#print axioms StatementRun.exn_declared

end InitECandidate.Runtime.FineCost
