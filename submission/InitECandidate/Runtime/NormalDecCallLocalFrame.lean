import InitECandidate.Runtime.NormalDecLocalFrame
import InitECandidate.Runtime.PanDecCallUnconditionalNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Caller-local restoration lifts a normal continuation frame through an
opaque call, independently of the callee's private locals. -/
theorem normalLocalFrame_decCall (key name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (body : ProgHOL 64) (different : name ≠ key)
    (child : ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState state body = (none,post) → post.locals.lookup key = state.locals.lookup key) :
    ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState state (.decCall name shape function arguments body) = (none,post) →
        post.locals.lookup key = state.locals.lookup key := by
  intro F state post run
  obtain ⟨value,ready,output,locals,bodyRun,scope⟩ :=
    evaluate_decCall_unconditional_normal_scope state post name function shape arguments body run
  have kept := child (setVarHOLFinite name value ready) output bodyRun
  rw [scope]
  change (HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)).lookup key = _
  rw [restore_other_local _ name key _ (Ne.symm different)]
  simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different,locals] using kept

#print axioms normalLocalFrame_decCall
end InitECandidate.Runtime
