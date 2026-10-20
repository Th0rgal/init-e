import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A returned handler-free tail call exposes its actual callee execution.
The real callee's value is forwarded and its local map is cleared. -/
theorem evaluate_tail_call_returned_body {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (function : MlS)
 (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
 (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
 (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) arguments=some values)
 (lookup : lookupCodeHOLFinite s.code.lookup function values=some (body,callee,returnShape))
 (run : evaluateHOLFiniteState s (.call none function arguments)=(some (.returned value),post)) :
 ∃output,evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body=(some (.returned value),output) ∧
  post=emptyLocalsHOLFinite output := by
 rw [evaluateHOLFiniteState_call,args] at run
 simp only at run
 rw [lookup] at run
 simp only at run
 split at run
 · cases run
 · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
   | mk result output=>
    rw [bodyRun] at run
    cases result with
    | none=>cases run
    | some result=>
     cases result with
     | returned returnedValue=>
      simp only at run
      split at run
      · have same:=Prod.mk.inj run
        have equal : returnedValue=value:=PanSemResultExact.returned.inj (Option.some.inj same.1)
        subst returnedValue
        exact ⟨output,rfl,same.2.symm⟩
      · cases run
     | error=>cases run
     | timeOut=>cases run
     | «break»=>cases run
     | «continue»=>cases run
     | finalFfi ffi=>cases run
     | exception exceptionId thrown=>cases run

#print axioms evaluate_tail_call_returned_body
end InitECandidate.Runtime
