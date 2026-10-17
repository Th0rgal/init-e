import InitECandidate.Runtime.PanFreshLocalClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

private theorem updateEq_update (locals : HolFiniteMapExact MlS (ValueHOL 64)) (name : MlS) (value : ValueHOL 64) :
    locals.updateEq (name,value) = locals.update (name,value) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateEq,HolFiniteMapExact.lookup_update,FUPDATE_HOL_eq_FUPDATE]

/-- An unused logical local preserves the result and every nonlocal state field. -/
theorem evaluate_fresh_local_nonlocal_state {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : ValueHOL 64) (program : ProgHOL 64)
    (fresh : name ∉ freeVarIdsHOL program) :
    (evaluateHOLFiniteState (setVarHOLFinite name value state) program).1 = (evaluateHOLFiniteState state program).1 ∧
    emptyLocalsHOLFinite (evaluateHOLFiniteState (setVarHOLFinite name value state) program).2 =
      emptyLocalsHOLFinite (evaluateHOLFiniteState state program).2 := by
  obtain ⟨locals,run,_⟩ := PanGlobalsFreshLocalAssembly.evaluateFreshLocalHOL name value program state
    (evaluateHOLFiniteState state program).1 (evaluateHOLFiniteState state program).2 ⟨fresh,rfl⟩
  have actual : evaluateHOLFiniteState (setVarHOLFinite name value state) program =
      ((evaluateHOLFiniteState state program).1,{(evaluateHOLFiniteState state program).2 with locals := locals}) := by
    simpa only [updateEq_update,setVarHOLFinite] using run
  rw [actual]
  exact ⟨rfl,rfl⟩

#print axioms evaluate_fresh_local_nonlocal_state
end InitECandidate.Runtime
