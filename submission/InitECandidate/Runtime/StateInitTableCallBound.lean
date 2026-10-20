import InitECandidate.Runtime.StateInitHeapCallNormal
import InitECandidate.Runtime.StateInitFinalTailBound
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Fixed constructor calls are bounded even when one of their allocations fails. -/
theorem runBounded_state_init_table_call {F : Type} (s : PanSemStateFiniteExact 64 F)
 (width capacity : BitVec 64) (name : MlS) (code : s.code=originalRuntimeCode)
 (heap : StateInitHeapReady s) (budget : htabNewCost capacity+1≤s.clock) :
 RunBounded s (.call (some (some (.local,name),none)) (ofString "htab_new") [.const width,.const capacity])
 (htabNewCost capacity+1) := by
 obtain ⟨pointer,atHeap,aligned,capped⟩ := heap
 let callee : HolFiniteMapExact MlS (ValueHOL 64) := (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word width))).update
  (ofString "cap",.val (.word capacity))
 let entry := callEntryStateHOLFinite s callee
 have args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address))
  [.const width,.const capacity] = some [.val (.word width),.val (.word capacity)] := by
  rw [evalListHOLFinite_eq_toExact];rfl
 have lookup := htabNew_installed s width capacity code
 have bound := evaluate_htabNew_body_bounded entry width capacity pointer code
  (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  atHeap aligned capped (by change htabNewCost capacity≤s.clock-1;omega)
 cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_new) with
 | mk result post =>
  unfold RunBounded at bound
  rw [run] at bound
  obtain ⟨spent,remaining,safe⟩ := bound
  have call := evaluate_call_body_clock_no_timeout s post (ofString "htab_new") (some (.local,name))
   [.const width,.const capacity] [.val (.word width),.val (.word capacity)]
   (sourceFunctionBody Guest.guestFn_htab_new) callee .one result args lookup (by omega) run safe
  refine ⟨?_,?_,call.1⟩
  · rw [call.2];change s.clock-1≤post.clock+htabNewCost capacity at spent;omega
  · rw [call.2];change post.clock≤s.clock-1 at remaining;omega
#print axioms runBounded_state_init_table_call
end InitECandidate.Runtime
