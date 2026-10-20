import InitECandidate.Runtime.StateFreshTxRuntimeBound
import InitECandidate.Runtime.OriginalStateFreshTxCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The actual installed state_fresh_tx call, including every allocation,
store and error outcome. Its bound assumes only the real typed/capped heap,
not room for the eight new tables. -/
theorem state_fresh_tx_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (code : s.code=originalRuntimeCode) (heap : StateInitHeapReady s) (budget : 1001≤s.clock) :
 RunBounded s (.call (some (none,none)) (ofString "state_fresh_tx") []) 1001 := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty
 let entry:=callEntryStateHOLFinite s callee
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) []=some [] := rfl
 have installed : s.code.lookup (ofString "state_fresh_tx")=
  some ([],sourceFunctionBody Guest.guestFn_state_fresh_tx,.one) := by
  rw [code];exact originalRuntimeCode_stateFreshTx_lookup
 have lookup:=pan_no_args_lookup s.code.lookup (ofString "state_fresh_tx")
  (sourceFunctionBody Guest.guestFn_state_fresh_tx) installed
 have bound:=state_fresh_tx_body_bounded entry code heap (by change 1000≤s.clock-1;omega)
 cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_state_fresh_tx) with
 | mk result post =>
  unfold RunBounded at bound
  rw [run] at bound
  obtain ⟨spent,remaining,safe⟩:=bound
  have call:=evaluate_call_body_clock_no_timeout s post (ofString "state_fresh_tx") none [] []
   (sourceFunctionBody Guest.guestFn_state_fresh_tx) callee .one result args lookup (by omega) run safe
  refine ⟨?_,?_,call.1⟩
  · rw [call.2];change s.clock-1≤post.clock+1000 at spent;omega
  · rw [call.2];change post.clock≤s.clock-1 at remaining;omega
#print axioms state_fresh_tx_call_bounded
end InitECandidate.Runtime
