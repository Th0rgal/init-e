import InitECandidate.Runtime.DecodeStepListUniformBound
import InitECandidate.Runtime.DecodeStepPrefixRecordMetadata
import InitECandidate.Runtime.DecodeStepListReturnedHeap
import InitECandidate.Runtime.DecodeStepBranchReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_list_push_returned_fields {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (budget : decodeStepTwoCaseCost inputLimit ≤ s.clock) (record : BitVec 64)
    (run : evaluateHOLFiniteState s (decodeStepAt 6) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    ∃ stage : BitVec 64, (stage=1 ∧ count=2 ∨ stage=2 ∧ count=17) ∧
      DecoderRecordFields post record array pointer length stage := by
  by_cases two : count = 2
  · subst count
    obtain ⟨p0,n0,entry0⟩ := table 0 (by decide)
    obtain ⟨p1,n1,entry1⟩ := table 1 (by decide)
    rw [evaluate_decode_step_two_items s array atSlices] at run
    have small : n0.toNat ≤ inputLimit := (entry0.length_bound s array 0 p0 n0 input inputLength).trans inputBound
    have product : n0.toNat*((2*n0.toNat+1)*15+19) ≤ inputLimit*((2*inputLimit+1)*15+19) :=
      Nat.mul_le_mul small (by omega)
    have divided : n0.toNat/4 ≤ inputLimit/4 := Nat.div_le_div_right small
    refine ⟨1,Or.inl ⟨rfl,rfl⟩,?_⟩
    exact decode_step_two_case_push_returned_fields s post array p0 n0 scratch frame record pointer length ceiling inputLimit
      atPointer atLength atArray entry0.readable entry0.noWrap small (by omega) scratchGlobal frameGlobal code ordered
      framePositive scratchBelow arena (by unfold decodeStepTwoCaseCost at budget; omega) run
  · by_cases seventeen : count = 17
    · subst count
      rw [evaluate_decode_step_seventeen s array atSlices] at run
      have recordEq := push_pair_record_eq record _ (decode_step_branch_construction_returned_pointer s post scratch frame _
        code (by unfold decodeStepTwoCaseCost at budget; omega) scratchGlobal frameGlobal ordered run)
      refine ⟨2,Or.inr ⟨rfl,rfl⟩,?_⟩
      rw [recordEq]
      exact decode_step_branch_construction_returned_fields s post scratch frame array pointer length atArray atPointer atLength
        scratchGlobal frameGlobal ordered code (by unfold decodeStepTwoCaseCost at budget; omega) _ run
    · rw [evaluate_decode_step_invalid_arity s array count two seventeen code atSlices] at run
      exact False.elim (evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 4] _ (congrArg Prod.fst run))

#print axioms decode_step_list_push_returned_fields
end InitECandidate.Runtime
