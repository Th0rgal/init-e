import InitECandidate.Runtime.AccessListLoopHeapFloor
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful traversal never moves its heap pointer backward. -/
theorem access_loop_normal_heap_lower_bound {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (run : evaluateHOLFiniteState state accessLoop = (none,post)) :
    ∃ heap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      valid.heap.toNat ≤ heap.toNat := by
  obtain ⟨result,output,evaluated,_,_,_,done,_⟩ := evaluate_access_loop_heap_floor_bounded state array count records input inputLength scratch frame
    ceiling inputLimit valid inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeRecords countLimit inputBeforeFrame
    valid.heap.toNat (Nat.le_refl _) budget
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (evaluated.symm.trans run)
  obtain ⟨next,_,bounded⟩ := done rfl
  exact ⟨next.heap,next.heapGlobal,bounded⟩

#print axioms access_loop_normal_heap_lower_bound
end InitECandidate.Runtime
