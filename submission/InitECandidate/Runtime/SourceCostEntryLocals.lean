import InitECandidate.Runtime.SourceCostGlobalsCallBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! A destination-free call without arguments does not read the caller's
locals: its run from the caller state with emptied locals has the same events. -/

theorem entry_plan_none {F : Type} (s s' bodyPost : PanSemStateFiniteExact 64 F) returnShape bodyResult :
    callCostPlan s none returnShape bodyResult bodyPost =
      callCostPlan s' none returnShape bodyResult bodyPost := by
  unfold callCostPlan; rfl

theorem entry_empty_locals {F : Type} {s post : PanSemStateFiniteExact 64 F} {function : MlStringHOL}
    {r ev} (run : StatementRun s (.call none function []) r post ev) :
    ∃ post', StatementRun (emptyLocalsHOLFinite s) (.call none function []) r post' ev := by
  have argsEmpty : evalListHOLFinite (emptyLocalsHOLFinite s)
      (h := fun a => Classical.propDecidable ((emptyLocalsHOLFinite s).memaddrs a)) [] = some [] := by
    simp [evalListHOLFinite, evalListHOLExact]
  cases run with
  | callDone args lookup clock bodyRun plan =>
    have values : _ := args
    simp [evalListHOLFinite, evalListHOLExact] at values
    subst values
    rw [entry_plan_none s (emptyLocalsHOLFinite s)] at plan
    have h := StatementRun.callDone (s := emptyLocalsHOLFinite s) argsEmpty lookup clock bodyRun plan
    simp only [expressionListEvents] at h ⊢
    exact ⟨_, h⟩
  | callHandler args lookup clock bodyRun plan handlerRun =>
    obtain ⟨_, _, _, h⟩ := globals_plan_handler_info plan
    cases h
  | callArgumentsFailure args =>
    simp [evalListHOLFinite, evalListHOLExact] at args
  | callLookupFailure args lookup =>
    have values : _ := args
    simp [evalListHOLFinite, evalListHOLExact] at values
    subst values
    have h := StatementRun.callLookupFailure (s := emptyLocalsHOLFinite s) (info := none) argsEmpty lookup
    simp only [expressionListEvents] at h ⊢
    exact ⟨_, h⟩
  | callTimeout args lookup clock =>
    have values : _ := args
    simp [evalListHOLFinite, evalListHOLExact] at values
    subst values
    have h := StatementRun.callTimeout (s := emptyLocalsHOLFinite s) (info := none) argsEmpty lookup clock
    simp only [expressionListEvents, callGlobalEvents] at h ⊢
    exact ⟨_, h⟩

#print axioms entry_empty_locals
end InitECandidate.Runtime.FineCost
