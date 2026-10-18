import InitECandidate.Runtime.PanDecCallReturnedGlobalScope
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Every returned declaration-call reaches its real continuation with caller
locals and unchanged code, regardless of the callee's memory/global effects. -/
theorem evaluate_decCall_returned_continuation {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) =
      (some (.returned finalValue),post)) :
    ∃ (value : ValueHOL 64) (ready output : PanSemStateFiniteExact 64 F),
      ready.locals = state.locals ∧ ready.code = state.code ∧
      evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation =
        (some (.returned finalValue),output) ∧ post.globals = output.globals := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_decCall_total,args] at run; cases run
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_decCall_lookup_none state name shape function arguments continuation values args lookup] at run; cases run
    | some found =>
      obtain ⟨body,callee,returnShape⟩ := found
      obtain ⟨value,bodyPost,ready,output,bodyRun,locals,_,_,_,code,tail,postEq⟩ :=
        evaluate_decCall_returned_global_scope state post name function shape returnShape arguments values
          body continuation callee finalValue args lookup run
      have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
      rw [bodyRun] at meta'
      exact ⟨value,ready,output,locals,code.trans meta'.1,tail,by rw [postEq]⟩

#print axioms evaluate_decCall_returned_continuation
end InitECandidate.Runtime
