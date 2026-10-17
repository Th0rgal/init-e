import InitECandidate.Runtime.PanDecCallNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Lift a continuation's local frame through a real normally completed
call, using caller-local restoration rather than any callee-local invariant. -/
theorem evaluate_decCall_normal_local_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function key : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (different : key ≠ name)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (frame : ∀ (value : ValueHOL 64) (ready output : PanSemStateFiniteExact 64 F), ready.locals = state.locals →
      evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation = (none,output) →
      output.locals.lookup key = (setVarHOLFinite name value ready).locals.lookup key)
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  obtain ⟨value,ready,output,locals,tail,restored⟩ :=
    evaluate_decCall_normal_scope state post name function shape returnShape arguments values body continuation callee args lookup run
  rw [restored,saved_local_lookup_other output.locals name key _ different,frame value ready output locals tail]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]

#print axioms evaluate_decCall_normal_local_frame
end InitECandidate.Runtime
