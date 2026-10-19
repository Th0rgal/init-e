import InitECandidate.Runtime.DecodeStepTwoCaseUniformBound
import InitECandidate.Runtime.DecodeStepListPushProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every original list-node arity is bounded: two-item compact paths, real
seventeen-item branches, and invalid arity rejection. -/
theorem runBounded_decode_step_list_dispatch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength heap scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)]))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitCap : inputLimit ≤ 134217712)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat % 8 = 0)
    (tableBefore : array.toNat + count.toNat*16 ≤ heap.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch)
    (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepTwoCaseCost inputLimit ≤ s.clock) :
    RunBounded s (decodeStepAt 6) (decodeStepTwoCaseCost inputLimit) := by
  have cost : 43 ≤ decodeStepTwoCaseCost inputLimit := by unfold decodeStepTwoCaseCost; omega
  by_cases two : count = 2
  · subst count
    obtain ⟨p0,n0,entry0⟩ := table 0 (by decide)
    obtain ⟨p1,n1,entry1⟩ := table 1 (by decide)
    unfold RunBounded
    rw [evaluate_decode_step_two_items s array atSlices]
    exact runBounded_decode_step_two_case s array p0 n0 p1 n1 heap scratch frame ceiling inputLimit atArray
      entry0.readable entry1.readable entry0.noWrap entry1.noWrap
      ((entry0.length_bound s array 0 p0 n0 input inputLength).trans inputBound)
      ((entry1.length_bound s array 1 p1 n1 input inputLength).trans inputBound)
      limitCap atHeap heapBound aligned (by simpa using tableBefore) arrayAbove scratchGlobal frameGlobal code
      ordered framePositive scratchBelow arena budget
  · by_cases seventeen : count = 17
    · subst count
      exact (runBounded_decode_step_seventeen s array scratch frame atSlices scratchGlobal frameGlobal code
        (cost.trans budget)).weaken cost
    · unfold RunBounded
      rw [evaluate_decode_step_invalid_arity s array count two seventeen code atSlices]
      have bounded := evaluate_mptFail_call_bounded s (.const 4) 4 code (by omega)
        (by rw [evalListHOLFinite_eq_toExact]; rfl)
      exact (show RunBounded s (.call (some (none,none)) (ofString "mpt_fail") [.const 4]) 1 from
        ⟨by rw [bounded.1]; omega,by rw [bounded.1]; omega,bounded.2.1⟩).weaken (by omega)

#print axioms runBounded_decode_step_list_dispatch
end InitECandidate.Runtime
