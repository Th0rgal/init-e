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

/-- Re-dispatching a non-error destination-free call result through a
destination-free call with the callee's return shape is non-error. -/
theorem entry_plan_ok {F : Type} {s post : PanSemStateFiniteExact 64 F} {function : MlStringHOL}
    {r ev} (run : StatementRun s (.call none function []) r post ev) (ok : r ≠ some .error)
    {body callee returnShape}
    (lookup : lookupCodeHOLFinite s.code.lookup function [] = some (body, callee, returnShape))
    (s' bodyPost : PanSemStateFiniteExact 64 F) {res p}
    (plan : callCostPlan s' none returnShape r bodyPost = .done res p) : res ≠ some .error := by
  cases run with
  | @callDone _ _ _ _ _ _ _ _ bodyResult _ _ _ _ args lookup' clock bodyRun plan0 =>
    have values : _ := args
    simp [evalListHOLFinite, evalListHOLExact] at values
    subst values
    rw [lookup] at lookup'
    simp only [Option.some.injEq, Prod.mk.injEq] at lookup'
    obtain ⟨-, -, rfl⟩ := lookup'
    unfold callCostPlan at plan0 plan
    rcases bodyResult with _ | (_ | _ | _ | _ | v | ⟨eid, v⟩ | _)
    all_goals simp only at plan0
    all_goals (try (cases plan0; exact absurd rfl ok))
    all_goals first
      | (cases plan0; simp only at plan; cases plan; simp; done)
      | (split at plan0
         · rename_i hshape
           cases plan0
           simp only [hshape, ↓reduceIte] at plan
           cases plan; simp
         · cases plan0; exact absurd rfl ok)
  | callHandler args lookup clock bodyRun plan0 handlerRun =>
    obtain ⟨_, _, _, h⟩ := globals_plan_handler_info plan0
    cases h
  | callArgumentsFailure args => exact absurd rfl ok
  | callLookupFailure args lookup => exact absurd rfl ok
  | callTimeout args lookup clock =>
    unfold callCostPlan at plan
    cases plan; simp

theorem entry_lookup_noargs {code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {function : MlS} {body : ProgHOL 64} {returnShape : ShapeHOL}
    (found : code.lookup function = some ([], body, returnShape)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code.lookup function [] = some (body, HolFiniteMapExact.empty, returnShape) := by
  have hexact : lookupCodeHOLExact code.lookup function [] = some (body, fun _ => none, returnShape) := by
    unfold lookupCodeHOLExact; rw [found]; simp
  rcases hc : PanSemStateFiniteExact.lookupCodeHOLFinite code.lookup function [] with _ | ⟨b, c, rs⟩
  · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hc
    split at hc
    · rename_i h; rw [hexact] at h; cases h
    · cases hc
  · have e := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hc
    rw [hexact] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, hl, rfl⟩ := e
    rw [holFiniteMapExact_eq_of_lookup_eq (m := c) (n := HolFiniteMapExact.empty) (by rw [← hl]; rfl)]

#print axioms entry_plan_ok
#print axioms entry_empty_locals
end InitECandidate.Runtime.FineCost
