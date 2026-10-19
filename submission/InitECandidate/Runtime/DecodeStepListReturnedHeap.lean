import InitECandidate.Runtime.DecodeStepListUniformBound
import InitECandidate.Runtime.DecodeStepTwoCaseReturnedHeap
import InitECandidate.Runtime.DecodeStepBranchReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_list_returned_heap_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count input inputLength heap scratch frame pointer length : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
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
    (budget : decodeStepTwoCaseCost inputLimit ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (decodeStepAt 6) =
      (some (.returned value),post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      heap.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat%8=0 ∧
      ∀ watched : BitVec 64, ceiling ≤ watched.toNat → watched.toNat < heap.toNat →
        post.memory watched = s.memory watched := by
  by_cases two : count = 2
  · subst count
    obtain ⟨p0,n0,entry0⟩ := table 0 (by decide)
    obtain ⟨p1,n1,entry1⟩ := table 1 (by decide)
    rw [evaluate_decode_step_two_items s array atSlices] at run
    exact decode_step_two_case_returned_heap_contract s post array p0 n0 p1 n1 heap scratch frame pointer length ceiling inputLimit atArray atPointer atLength
      entry0.readable entry1.readable entry0.noWrap entry1.noWrap
      ((entry0.length_bound s array 0 p0 n0 input inputLength).trans inputBound)
      ((entry1.length_bound s array 1 p1 n1 input inputLength).trans inputBound)
      limitCap atHeap heapBound aligned (by simpa using tableBefore) arrayAbove scratchGlobal frameGlobal code
      ordered framePositive scratchBelow arena budget value run
  · by_cases seventeen : count = 17
    · subst count
      rw [evaluate_decode_step_seventeen s array atSlices] at run
      obtain ⟨heapPost,growth,capped,finishAligned,memory⟩ := decode_step_branch_construction_returned_heap_contract
        s post heap scratch frame array pointer length atHeap heapBound aligned atArray atPointer atLength
        scratchGlobal frameGlobal ordered code (by unfold decodeStepTwoCaseCost at budget; omega) value run
      exact ⟨allocationEnd heap 176,heapPost,growth,capped,finishAligned,
        fun watched above before => memory watched (by omega) before⟩
    · rw [evaluate_decode_step_invalid_arity s array count two seventeen code atSlices] at run
      exact False.elim (evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 4] _ (congrArg Prod.fst run))

#print axioms decode_step_list_returned_heap_contract
end InitECandidate.Runtime
