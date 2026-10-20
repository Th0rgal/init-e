import InitECandidate.Runtime.StateFreshTxHeapAdvance
import InitECandidate.Runtime.StateFreshTxCallRuntimeBound
import InitECandidate.Runtime.SystemMessageGasSetup
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The actual first system-transaction call reaches ext_code_of with all
caller operands, code/domain and a usable heap, or rejects within 1001 clocks.
No successful constructor or reserve is supplied as a premise. -/
theorem system_fresh_tx_entry_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (code : s.code=originalRuntimeCode) (heap : StateInitHeapReady s) (budget : 1001≤s.clock) :
 Reaches s (systemTransactionAt 0) (fun next=>next.locals=s.locals ∧next.code=s.code ∧
  next.memaddrs=s.memaddrs ∧StateInitHeapReady next) 1001 (systemTransactionAt 1) := by
 change Reaches s (.seq (.call (some (none,none)) (ofString "state_fresh_tx") []) (systemTransactionAt 1)) _ _ _
 apply reaches_seq
 have bound:=state_fresh_tx_call_bounded s code heap budget
 unfold RunBounded at bound
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "state_fresh_tx") [])
 have control:=evaluate_handlerFree_call_control s none (ofString "state_fresh_tx") []
 cases run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "state_fresh_tx") []) with
 | mk result post =>
  have spent : s.clock≤post.clock+1001 := by rw [run] at bound;exact bound.1
  have remaining : post.clock≤s.clock := by rw [run] at bound;exact bound.2.1
  have safe : result≠some .timeOut := by rw [run] at bound;exact bound.2.2
  rw [run] at metadata control
  cases result with
  | none =>
   have locals:=evaluate_discard_call_success_locals s (ofString "state_fresh_tx") [] (by rw [run])
   rw [run] at locals
   exact Or.inl ⟨post,⟨locals,metadata.1,metadata.2.1,state_fresh_tx_call_normal_heap s post code heap run⟩,
    spent,remaining,rfl⟩
  | some result =>
   exact Or.inr ⟨result,rfl,(fun v equal=>control.2.2 v (by rw [equal])),spent,remaining,fun _=>
    fun equal=>safe (by rw [equal])⟩
#print axioms system_fresh_tx_entry_reaches
end InitECandidate.Runtime
