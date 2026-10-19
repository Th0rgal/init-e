import InitECandidate.Runtime.DecodeStepListUniformBound
import InitECandidate.Runtime.DecodeCompletedNodeTwo
import InitECandidate.Runtime.DecodeStepBranchReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_list_completed_node {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (budget : decodeStepTwoCaseCost inputLimit ≤ s.clock) (value : ValueHOL 64) (node : BitVec 64)
    (completed : value=.rStruct [.val (.word (0#64)),.val (.word node)])
    (run : evaluateHOLFiniteState s (decodeStepAt 6) =
      (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
  by_cases two : count = 2
  · subst count
    obtain ⟨p0,n0,entry0⟩ := table 0 (by decide)
    obtain ⟨p1,n1,entry1⟩ := table 1 (by decide)
    rw [evaluate_decode_step_two_items s array atSlices] at run
    exact decode_step_two_case_completed_node s post array p0 n0 p1 n1 heap scratch frame pointer length ceiling inputLimit atArray atPointer atLength
      entry0.readable entry1.readable entry0.noWrap entry1.noWrap
      ((entry0.length_bound s array 0 p0 n0 input inputLength).trans inputBound)
      ((entry1.length_bound s array 1 p1 n1 input inputLength).trans inputBound)
      limitCap atHeap heapBound aligned (by simpa using tableBefore) arrayAbove scratchGlobal frameGlobal code
      ordered framePositive scratchBelow arena budget value node completed run
  · by_cases seventeen : count = 17
    · subst count
      rw [evaluate_decode_step_seventeen s array atSlices] at run
      have certified : returnedPairTagSyntax [1] decodeStepBranchConstruction = true := by
        simp only [decodeStepBranchConstruction,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
        rfl
      obtain ⟨tag,record,member,same⟩ := evaluate_returnedPairTagSyntax [1] _ certified s post value run
      have one : tag=1 := by simpa using member
      subst tag
      rw [completed] at same
      have firstEq := (List.cons.inj (ValueHOL.rStruct.inj same)).1
      have impossible : (0 : BitVec 64)=1 := HolWordLab.word.inj (ValueHOL.val.inj firstEq)
      exact False.elim ((by decide : (0 : BitVec 64)≠1) impossible)
    · rw [evaluate_decode_step_invalid_arity s array count two seventeen code atSlices] at run
      exact False.elim (evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 4] _ (congrArg Prod.fst run))

#print axioms decode_step_list_completed_node
end InitECandidate.Runtime
