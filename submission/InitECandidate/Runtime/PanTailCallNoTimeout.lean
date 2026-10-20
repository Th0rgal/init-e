import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A tail call cannot introduce timeout after a non-timeout actual callee. -/
theorem evaluate_tailCall_no_timeout {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (returnShape : ShapeHOL) (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state
      (h := fun address=>Classical.propDecidable (state.memaddrs address)) arguments=some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values=some (body,callee,returnShape))
    (nonzero : state.clock≠0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body=(result,post))
    (safe : result≠some .timeOut) :
    (evaluateHOLFiniteState state (.call none function arguments)).1≠some .timeOut := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,run]
  cases result with
  | none => simp
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split <;> simp

#print axioms evaluate_tailCall_no_timeout
end InitECandidate.Runtime
