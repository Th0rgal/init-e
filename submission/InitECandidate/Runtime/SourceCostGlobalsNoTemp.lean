import InitECandidate.Runtime.SourceCostGlobalsReady
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

theorem globals_validExact_ne {F : Type} {s : PanSemStateFiniteExact 64 F} {name : MlS} {value : ValueHOL 64}
    (valid : isValidValueHOLExact s.toExact .local name value = true)
    (h : s.locals.lookup globalsTemp = none) : name ≠ globalsTemp := by
  intro e; subst e
  simp [isValidValueHOLExact, lookupKvarHOLExact, toExact, h] at valid

theorem globals_setKvar_noTemp {F : Type} (s base : PanSemStateFiniteExact 64 F) {kind name value}
    (same : base.locals = s.locals) (valid : isValidValueHOLExact s.toExact kind name value = true)
    (h : s.locals.lookup globalsTemp = none) :
    (setKvarHOLFinite kind name value base).locals.lookup globalsTemp = none := by
  cases kind
  · have ne := globals_validExact_ne valid h
    rw [← same] at h
    exact globals_noTemp_setVar ne _ h
  · simp only [setKvarHOLFinite, setGlobalHOLFinite]; rw [same]; exact h

theorem globals_plan_done_noTemp {F : Type} {s bodyPost post : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult result}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post)
    (hs : s.locals.lookup globalsTemp = none) (hb : bodyPost.locals.lookup globalsTemp = none) :
    post.locals.lookup globalsTemp = none := by
  unfold callCostPlan at plan
  repeat' split at plan
  all_goals (cases plan)
  all_goals first
    | assumption
    | rfl
    | (exact globals_setKvar_noTemp s _ rfl (by assumption) hs)

theorem globals_plan_handler_info {F : Type} {s bodyPost entry : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult program}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    ∃ dest exception handlerVar, info = some (dest, some (exception, handlerVar, program)) := by
  unfold callCostPlan at plan
  repeat' split at plan
  all_goals (cases plan)
  all_goals first | exact ⟨_, _, _, rfl⟩ | (refine ⟨_, _, _, ?_⟩; assumption)

theorem globals_plan_handler_noTemp {F : Type} {s bodyPost entry : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult program}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program)
    (hs : s.locals.lookup globalsTemp = none) :
    entry.locals.lookup globalsTemp = none := by
  unfold callCostPlan at plan
  repeat' split at plan
  all_goals (cases plan)
  rename_i valid
  simp only [Bool.and_eq_true] at valid
  exact globals_noTemp_setVar (globals_validExact_ne valid.2 hs) _ hs

theorem globals_plan_handler_ready {F : Type} {s bodyPost entry : PanSemStateFiniteExact 64 F}
    {info function arguments returnShape bodyResult program}
    (ready : globalsReadyProg (.call info function arguments) = true)
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    globalsReadyProg program = true := by
  obtain ⟨dest, exception, handlerVar, rfl⟩ := globals_plan_handler_info plan
  rcases dest with _ | ⟨kind, name⟩
  · simp only [globalsReadyProg, Bool.and_eq_true] at ready; exact ready.2
  · cases kind
    · simp only [globalsReadyProg, Bool.and_eq_true] at ready; exact ready.2
    · simp [globalsReadyProg] at ready

theorem globals_stopPlan_noTemp {F : Type} (bodyResult : Option (PanSemResultExact 64))
    {bodyPost : PanSemStateFiniteExact 64 F} (hb : bodyPost.locals.lookup globalsTemp = none) :
    (declareCallStopPlan bodyResult bodyPost).2.locals.lookup globalsTemp = none := by
  unfold declareCallStopPlan
  split <;> dsimp only <;> first | exact hb | rfl

theorem globals_entry_ready {F : Type} {s : PanSemStateFiniteExact 64 F} (code : GlobalsCodeReady s.code)
    {function : MlS} {values : List (ValueHOL 64)} {body callee returnShape}
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape)) :
    globalsReadyProg body = true ∧ (callEntryStateHOLFinite s callee).locals.lookup globalsTemp = none ∧
      GlobalsCodeReady (callEntryStateHOLFinite s callee).code := by
  obtain ⟨vshapes, found, _⟩ :=
    lookupCodeHOLFinite_some_inv s.code.lookup function values body callee returnShape lookup
  exact ⟨(code function vshapes body returnShape found).1, globals_callee_noTemp code lookup, code⟩

theorem globals_setKvarExact_noTemp {F : Type} {s : PanSemStateFiniteExact 64 F} {kind name}
    {old value : ValueHOL 64} (found : lookupKvarHOLExact kind name s.toExact = some old)
    (h : s.locals.lookup globalsTemp = none) :
    (setKvarHOLExact kind name value s.toExact).locals globalsTemp = none := by
  cases kind
  · have ne : globalsTemp ≠ name := by
      intro e; subst e; simp [lookupKvarHOLExact, toExact, h] at found
    simp [setKvarHOLExact, ne, h]
  · exact h

theorem globals_ofExact_noTemp {F : Type} (m : PanSemStateExact 64 F) (support : m.FiniteSupport)
    (h : m.locals globalsTemp = none) : (ofExact m support).locals.lookup globalsTemp = none := h

/-- Ready programs never bind the `pan_globals` call temporary: a run from a
state without it ends in a state without it. -/
theorem StatementRun.noTemp {F : Type} {s post : PanSemStateFiniteExact 64 F} {p r ev}
    (run : StatementRun fn s p r post ev) :
    globalsReadyProg p = true → GlobalsCodeReady s.code →
      s.locals.lookup globalsTemp = none → post.locals.lookup globalsTemp = none := by
  induction run
  case seqNext one _ ih1 ih2 =>
    intro ready code h
    simp only [globalsReadyProg, Bool.and_eq_true] at ready
    exact ih2 ready.2 (by rw [one.code_eq]; exact code) (ih1 ready.1 code h)
  case seqStop ih =>
    intro ready code h
    simp only [globalsReadyProg, Bool.and_eq_true] at ready
    exact ih ready.1 code h
  case iteYes ih =>
    intro ready code h
    simp only [globalsReadyProg, Bool.and_eq_true] at ready
    exact ih ready.1.2 code h
  case iteNo ih =>
    intro ready code h
    simp only [globalsReadyProg, Bool.and_eq_true] at ready
    exact ih ready.2 code h
  case whileNext one _ ih1 ih2 =>
    intro ready code h
    have r := ready
    simp only [globalsReadyProg, Bool.and_eq_true] at r
    exact ih2 ready (by rw [one.code_eq]; exact code) (ih1 r.2 code h)
  case whileContinue one _ ih1 ih2 =>
    intro ready code h
    have r := ready
    simp only [globalsReadyProg, Bool.and_eq_true] at r
    exact ih2 ready (by rw [one.code_eq]; exact code) (ih1 r.2 code h)
  case whileBreak ih =>
    intro ready code h
    simp only [globalsReadyProg, Bool.and_eq_true] at ready
    exact ih ready.2 code h
  case whilePropagate ih =>
    intro ready code h
    simp only [globalsReadyProg, Bool.and_eq_true] at ready
    exact ih ready.2 code h
  case assignValue kind _ _ _ _ _ valid =>
    intro _ _ h
    cases kind
    · exact globals_noTemp_setVar (globals_valid_ne valid h) _ h
    · exact h
  case primitiveValue valid =>
    intro _ _ h
    exact globals_noTemp_setVar (globals_valid_ne valid h) _ h
  case declareValue ih =>
    intro ready code h
    simp only [globalsReadyProg, Bool.and_eq_true, bne_iff_ne] at ready
    exact globals_noTemp_resVar ready.1.1 _ (ih ready.2 code (globals_noTemp_setVar ready.1.1 _ h))
  case callDone lookup _ _ plan ihBody =>
    intro ready code h
    obtain ⟨readyBody, entry, entryCode⟩ := globals_entry_ready code lookup
    exact globals_plan_done_noTemp plan h (ihBody readyBody entryCode entry)
  case callHandler lookup _ bodyRun plan handlerRun ihBody ihHandler =>
    intro ready code h
    exact ihHandler (globals_plan_handler_ready ready plan)
      (by rw [globals_plan_handler_code plan, bodyRun.code_eq]; exact code)
      (globals_plan_handler_noTemp plan h)
  case declareCallReturn lookup _ bodyRun _ _ ihBody ihCont =>
    intro ready code h
    simp only [globalsReadyProg, Bool.and_eq_true, bne_iff_ne] at ready
    exact globals_noTemp_resVar ready.1.1 _
      (ihCont ready.2 (by simp only [setVarHOLFinite]; rw [bodyRun.code_eq]; exact code)
        (globals_noTemp_setVar ready.1.1 _ h))
  case declareCallRejectedReturn lookup _ _ _ ihBody =>
    intro ready code h
    obtain ⟨readyBody, entry, entryCode⟩ := globals_entry_ready code lookup
    exact ihBody readyBody entryCode entry
  case declareCallStopped lookup _ _ _ ihBody =>
    intro ready code h
    obtain ⟨readyBody, entry, entryCode⟩ := globals_entry_ready code lookup
    exact globals_stopPlan_noTemp _ (ihBody readyBody entryCode entry)
  case external run =>
    intro _ _ h
    rw [evaluateHOLFiniteState_extCall_source] at run
    repeat' split at run
    all_goals
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      first | rfl | exact h | (apply globals_ofExact_noTemp; exact h)
  case sharedStore run =>
    intro _ _ h
    rw [evaluateHOLFiniteState_shMemStore_total] at run
    simp only [] at run
    split at run
    · obtain ⟨_, rfl⟩ := Prod.mk.inj run
      apply globals_ofExact_noTemp
      unfold shMemStoreHOLExact
      repeat' split
      all_goals exact h
    · obtain ⟨_, rfl⟩ := Prod.mk.inj run; exact h
  case sharedLoad run =>
    intro ready _ h
    simp at run
    obtain ⟨_, rfl⟩ := run
    apply globals_ofExact_noTemp
    unfold shMemLoadClauseHOLFiniteExact shMemLoadClauseHOLExact
    split
    all_goals
      simp only []
      split
      all_goals first | exact h | (unfold shMemLoadHOLExact; repeat' split) <;>
        first | exact h | rfl | exact globals_setKvarExact_noTemp (by assumption) h
  all_goals intro ready code h
  all_goals first
    | assumption
    | rfl

#print axioms StatementRun.noTemp
end InitECandidate.Runtime.FineCost
