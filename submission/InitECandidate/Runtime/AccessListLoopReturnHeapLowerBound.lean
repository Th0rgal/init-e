import InitECandidate.Runtime.AccessListLoopReturnedResult
import InitECandidate.Runtime.AccessListLoopHeapLowerBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual return retains the traversal's cumulative heap-growth bound. -/
theorem access_loop_returned_heap_lower_bound {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (budget : (count.toNat - valid.index.toNat) *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state accessLoopAndReturn = (some (.returned value),post)) :
    ∃ heap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      valid.heap.toNat ≤ heap.toNat := by
  obtain ⟨middle,loopRun,_,restored⟩ := access_loop_returned_result state post array count records input inputLength scratch frame
    ceiling inputLimit valid inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeRecords countLimit inputBeforeFrame budget value run
  obtain ⟨heap,binding,bounded⟩ := access_loop_normal_heap_lower_bound state middle array count records input inputLength scratch frame
    ceiling inputLimit valid inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeRecords countLimit inputBeforeFrame budget loopRun
  rw [restored]
  exact ⟨heap,binding,bounded⟩

#print axioms access_loop_returned_heap_lower_bound
end InitECandidate.Runtime
