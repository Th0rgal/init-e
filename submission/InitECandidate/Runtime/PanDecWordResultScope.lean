import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Invert any outcome of a word-initialized declaration, exposing the real
body outcome before restoration of the declaration's previous local binding. -/
theorem evaluate_dec_word_result_scope {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (initializer : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64)
    (result : Option (PanSemResultExact 64))
    (evaluated : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) initializer = some (.val (.word word)))
    (run : evaluateHOLFiniteState state (.dec name .one initializer body) = (result,post)) :
    ∃ output, evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) state) body = (result,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  rw [evaluateHOLFiniteState_dec_total] at run
  simp only [evaluated,shapeOfHOLExact,shapeEqHOL,if_true] at run
  cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) state) body with
  | mk bodyResult output =>
    rw [bodyRun] at run
    have resultEq : bodyResult = result := (Prod.mk.inj run).1
    subst bodyResult
    exact ⟨output,rfl,(Prod.mk.inj run).2.symm⟩

#print axioms evaluate_dec_word_result_scope
end InitECandidate.Runtime
