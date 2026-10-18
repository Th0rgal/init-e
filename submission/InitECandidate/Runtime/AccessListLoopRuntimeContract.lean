import InitECandidate.Runtime.AccessListLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion exposes the retained slice array, globals and final heap reserve. -/
theorem access_loop_normal_runtime_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState state accessLoop = (none,post)) :
    ∃ heap : BitVec 64,
      post.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) ∧
      post.locals.lookup (ofString "recs") = some (.val (.word records)) ∧
      post.locals.lookup (ofString "i") = some (.val (.word count)) ∧
      RlpSliceInputPrefix post array input inputLength count.toNat ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      heap.toNat ≤ 33806089496 ∧ heap.toNat % 8 = 0 ∧
      input.toNat + inputLength.toNat ≤ heap.toNat ∧
      records.toNat + count.toNat * 24 ≤ heap.toNat ∧
      heap.toNat + inputLength.toNat * 32 + 7 ≤ frame.toNat := by
  obtain ⟨result,output,evaluated,_,_,_,done,_⟩ := evaluate_access_loop_bounded state array count records input inputLength scratch frame
    ceiling inputLimit valid inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeRecords countLimit inputBeforeFrame budget
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (evaluated.symm.trans run)
  obtain ⟨next,finished⟩ := done rfl
  refine ⟨next.heap,next.listLocal,next.recordsLocal,?_,next.slices,next.scratchGlobal,next.frameGlobal,next.heapGlobal,
    next.heapBound,next.heapAligned,next.inputBeforeHeap,next.recordsBeforeHeap,?_⟩
  · rw [← finished]; exact next.indexLocal
  · have reserve := next.reserve
    rw [finished] at reserve
    simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using reserve

#print axioms access_loop_normal_runtime_contract
end InitECandidate.Runtime
