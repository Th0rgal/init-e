import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem normalLocalFrame_dec (key name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64)
    (different : name ≠ key)
    (child : ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState state body = (none,post) → post.locals.lookup key = state.locals.lookup key) :
    ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState state (.dec name shape initializer body) = (none,post) →
        post.locals.lookup key = state.locals.lookup key := by
  intro F state post run
  obtain ⟨value,output,_,bodyRun,scope⟩ := evaluate_dec_normal_scope state post name shape initializer body run
  have kept := child (setVarHOLFinite name value state) output bodyRun
  rw [scope]
  change (HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)).lookup key = _
  rw [restore_other_local _ name key _ (Ne.symm different)]
  simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different] using kept

#print axioms normalLocalFrame_dec
end InitECandidate.Runtime
