import InitECandidate.Runtime.SourceCostGlobalsNoTemp
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Statement runs never remove a global: the source global domain only grows. -/

def GlobalsPresent {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) : Prop :=
  s.globals.lookup name ≠ none

theorem globals_setKvar_present {F : Type} {s base : PanSemStateFiniteExact 64 F} {kind name value}
    {key : MlS} (same : base.globals = s.globals) (h : GlobalsPresent s key) :
    GlobalsPresent (setKvarHOLFinite kind name value base) key := by
  unfold GlobalsPresent at *
  cases kind
  · simpa [setKvarHOLFinite, setVarHOLFinite, same] using h
  · simp only [setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    split
    · simp
    · rw [same]; exact h

theorem globals_ofExact_present {F : Type} {key : MlS}
    (m : PanSemStateExact 64 F) (support : m.FiniteSupport) (h : m.globals key ≠ none) :
    GlobalsPresent (ofExact m support) key := h

theorem globals_plan_done_present {F : Type} {s bodyPost post : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult result} {key : MlS}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post)
    (hb : GlobalsPresent bodyPost key) : GlobalsPresent post key := by
  unfold callCostPlan at plan
  repeat' split at plan
  all_goals (cases plan)
  all_goals first
    | exact hb
    | exact globals_setKvar_present (s := bodyPost) rfl hb

theorem globals_plan_handler_present {F : Type} {s bodyPost entry : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult program} {key : MlS}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program)
    (hb : GlobalsPresent bodyPost key) : GlobalsPresent entry key := by
  unfold callCostPlan at plan
  repeat' split at plan
  all_goals (cases plan)
  exact hb

theorem globals_stopPlan_present {F : Type} (bodyResult : Option (PanSemResultExact 64))
    {bodyPost : PanSemStateFiniteExact 64 F} {key : MlS} (hb : GlobalsPresent bodyPost key) :
    GlobalsPresent (declareCallStopPlan bodyResult bodyPost).2 key := by
  unfold declareCallStopPlan
  split <;> exact hb

theorem globals_setKvarExact_present {F : Type} {s : PanSemStateFiniteExact 64 F} {kind name}
    {value : ValueHOL 64} {key : MlS} (h : GlobalsPresent s key) :
    (setKvarHOLExact kind name value s.toExact).globals key ≠ none := by
  cases kind
  · exact h
  · simp only [setKvarHOLExact]
    split
    · simp
    · exact h

theorem StatementRun.globals_present {F : Type} {s post : PanSemStateFiniteExact 64 F} {p r ev}
    (run : StatementRun s p r post ev) (key : MlS) :
    GlobalsPresent s key → GlobalsPresent post key := by
  induction run
  case seqNext ih1 ih2 => exact fun h => ih2 (ih1 h)
  case whileNext ih1 ih2 => exact fun h => ih2 (ih1 h)
  case whileContinue ih1 ih2 => exact fun h => ih2 (ih1 h)
  case assignValue => exact fun h => globals_setKvar_present rfl h
  case callDone plan ih => exact fun h => globals_plan_done_present plan (ih h)
  case callHandler plan _ ihBody ihHandler =>
    exact fun h => ihHandler (globals_plan_handler_present plan (ihBody h))
  case declareCallReturn ihBody ihCont => exact fun h => ihCont (ihBody h)
  case declareCallStopped ih => exact fun h => globals_stopPlan_present _ (ih h)
  case external run =>
    intro h
    rw [evaluateHOLFiniteState_extCall_source] at run
    repeat' split at run
    all_goals
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      first | exact h | (apply globals_ofExact_present; exact h)
  case sharedStore run =>
    intro h
    rw [evaluateHOLFiniteState_shMemStore_total] at run
    simp only [] at run
    split at run
    · obtain ⟨_, rfl⟩ := Prod.mk.inj run
      apply globals_ofExact_present
      unfold shMemStoreHOLExact
      repeat' split
      all_goals exact h
    · obtain ⟨_, rfl⟩ := Prod.mk.inj run; exact h
  case sharedLoad run =>
    intro h
    simp at run
    obtain ⟨_, rfl⟩ := run
    apply globals_ofExact_present
    unfold shMemLoadClauseHOLFiniteExact shMemLoadClauseHOLExact
    split
    all_goals
      simp only []
      split
      all_goals first | exact h | (unfold shMemLoadHOLExact; repeat' split) <;>
        first | exact h | exact globals_setKvarExact_present h
  all_goals first
    | exact id
    | (intro h; assumption)
    | (rename_i ih; exact ih)

#print axioms StatementRun.globals_present
end InitECandidate.Runtime.FineCost
