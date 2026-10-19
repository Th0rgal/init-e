import InitECandidate.Runtime.HtrRequestListCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 2000000

def htrRequestListUniformCost : Nat := htrRequestListBodyCost (134217712#64)

theorem htrRequestList_cost_le_uniform (count : BitVec 64) (small : count.toNat ≤ 134217712) :
    htrRequestListBodyCost count ≤ htrRequestListUniformCost := by
  change 1 + (2 + (count.toNat * (htrRequestStepCost + 1) + (htrPlistChunksCost + 2))) ≤
    1 + (2 + (134217712 * (htrRequestStepCost + 1) + (htrPlistChunksCost + 2)))
  exact Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.add_le_add_right (Nat.mul_le_mul_right (htrRequestStepCost + 1) small) (htrPlistChunksCost + 2)) 2) 1

theorem runBounded_htrRequestList_call_uniform {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (kind pointer count size out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word kind),.val (.word pointer),.val (.word count),.val (.word size),.val (.word out)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : count.toNat ≤ 134217712) (cap : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrRequestListUniformCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_request_list") arguments) (htrRequestListUniformCost + 1) := by
  have le := Nat.add_le_add_right (htrRequestList_cost_le_uniform count small) 1
  exact (runBounded_htrRequestList_call state destination arguments kind pointer count size out heap args hh small cap code
    (le.trans budget)).weaken le

#print axioms htrRequestList_cost_le_uniform
#print axioms runBounded_htrRequestList_call_uniform
end InitECandidate.Runtime
