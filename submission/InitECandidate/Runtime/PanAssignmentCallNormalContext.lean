import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- A real normal assignment call exposes the actual returned callee and
exact assignment context, for either local or global destinations. -/
theorem assignment_call_normal_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (kind : VarKind) (name function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
 (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values)
 (lookup : lookupCodeHOLFinite s.code.lookup function values=some (body,callee,shape))
 (run : evaluateHOLFiniteState s (.call (some (some (kind,name),none)) function arguments)=(none,post)) :
 ∃value bodyPost,evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body=(some (.returned value),bodyPost) ∧
  post=setKvarHOLFinite kind name value {bodyPost with locals:=s.locals} := by
 rw [evaluateHOLFiniteState_call,args] at run
 simp only at run
 rw [lookup] at run
 simp only at run
 split at run
 · cases run
 · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
   | mk result bodyPost=>
    rw [bodyRun] at run
    cases result with
    | none=>cases run
    | some result=>
     cases result with
     | returned value=>
      simp only at run
      split at run
      · split at run
        · have remaining:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rw [bodyRun] at remaining
          refine ⟨value,bodyPost,rfl,?_⟩
          have same:=(Prod.mk.inj run).2.symm
          simpa [fixClockHOLFinite,Nat.not_lt.mpr remaining] using same
        · cases run
      · cases run
     | error=>cases run
     | timeOut=>cases run
     | «break»=>cases run
     | «continue»=>cases run
     | exception _ _=>cases run
     | finalFfi _=>cases run
#print axioms assignment_call_normal_context
end InitECandidate.Runtime
