import InitECandidate.Runtime.HtrRequestListGlobals
import InitECandidate.Runtime.HtrRequestListLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem htrRequestList_loop_heapGlobals :
    NormalRel HeapGlobalsRel (.while htrRequestListCondition htrRequestListStep) := by
  have pre := heapGlobalsRel_preorder
  unfold htrRequestListStep htrRequestListBranch
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_while pre
    | apply normalRel_seq pre
    | apply normalRel_ite pre
    | exact htrDeposit_call_heapGlobals _
    | exact htrWdreq_call_heapGlobals _
    | exact htrCons_call_heapGlobals _
    | exact htrBdep_call_heapGlobals _
    | exact htrBexit_call_heapGlobals _

theorem htrRequestList_loop_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind pointer size roots heap count : BitVec 64) (rank : Nat)
    (small : count.toNat ≤ 134217712) (cap : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode)
    (valid : HtrRequestListState kind pointer size roots heap count state rank)
    (budget : rank * (htrRequestStepCost + 1) ≤ state.clock)
    (run : evaluateHOLFiniteState state (.while htrRequestListCondition htrRequestListStep) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply htrRequestList_loop_heapGlobals (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have loop := htrRequestList_loop_ranked kind pointer size roots heap count small cap rank state code valid budget
  rw [run] at loop
  obtain ⟨_,next,_,_⟩ := loop.2.2.2 rfl
  apply HolFiniteMapExact.ext
  funext key
  by_cases same : key = ofString "heap_ptr"
  · subst key
    exact next.heapGlobal.trans valid.heapGlobal.symm
  · exact frame key same

#print axioms htrRequestList_loop_heapGlobals
#print axioms htrRequestList_loop_normal_globals
end InitECandidate.Runtime
