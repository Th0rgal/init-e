import InitECandidate.Runtime.CallBodyClockNoTimeout
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Exact handler-free call overhead, including every callee outcome. -/
theorem runBounded_discard_of_body {F : Type} (s : PanSemStateFiniteExact 64 F)
 (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
 (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL) (cost : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values)
 (lookup : lookupCodeHOLFinite s.code.lookup function values=some (body,callee,shape))
 (bound : RunBounded (callEntryStateHOLFinite s callee) body cost) (budget : cost+1≤s.clock) :
 RunBounded s (.call (some (none,none)) function arguments) (cost+1) := by
 cases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
 | mk result post=>
  unfold RunBounded at bound
  rw [run] at bound
  have transfer:=evaluate_call_body_clock_no_timeout s post function none arguments values body callee shape result
   args lookup (by omega) run bound.2.2
  refine ⟨?_,?_,transfer.1⟩
  · rw [transfer.2];have spent:=bound.1;change s.clock-1≤post.clock+cost at spent;omega
  · rw [transfer.2];have remaining:=bound.2.1;change post.clock≤s.clock-1 at remaining;omega

/-- A bounded non-returning prefix either reaches its actual normal continuation
or aborts within its real cost. -/
theorem reaches_seq_of_runBounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (first rest : ProgHOL 64) (cost : Nat) (P : PanSemStateFiniteExact 64 F→Prop)
 (bound : RunBounded s first cost)
 (noReturn : ∀value,(evaluateHOLFiniteState s first).1≠some (.returned value))
 (normal : ∀post,evaluateHOLFiniteState s first=(none,post)→P post) :
 Reaches s (.seq first rest) P cost rest := by
 apply reaches_seq
 cases run : evaluateHOLFiniteState s first with
 | mk result post=>
  unfold RunBounded at bound
  rw [run] at bound
  cases result with
  | none=>exact Or.inl ⟨post,normal post run,bound.1,bound.2.1,rfl⟩
  | some result=>
   exact Or.inr ⟨result,rfl,(fun value eq=>noReturn value (by rw [run];simp only;rw [eq])),bound.1,bound.2.1,
    fun _ eq=>bound.2.2 (by simp only;rw [eq])⟩
#print axioms runBounded_discard_of_body
#print axioms reaches_seq_of_runBounded
end InitECandidate.Runtime
