import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A real handler-free tail call never falls through to a next source
statement, including malformed arguments, failed lookup and zero clock. -/
theorem evaluate_tail_call_terminal {F : Type} (s : PanSemStateFiniteExact 64 F)
 (function : MlS) (arguments : List (ExpHOL 64)) :
 (evaluateHOLFiniteState s (.call none function arguments)).1≠none := by
 rw [evaluateHOLFiniteState_call]
 cases args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments with
 | none=>simp
 | some values=>
  simp only
  cases lookup : lookupCodeHOLFinite s.code.lookup function values with
  | none=>simp
  | some data=>
   obtain ⟨body,callee,returnShape⟩:=data
   simp only
   by_cases zero : s.clock=0
   · simp [zero]
   · simp only [if_neg zero]
     cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
     | mk result output=>
      cases result with
      | none=>simp
      | some result=>
       cases result <;>simp
       split <;>simp

#print axioms evaluate_tail_call_terminal
end InitECandidate.Runtime
