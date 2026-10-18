import InitECandidate.Runtime.AccessListLoopReturnedHeapResult
import InitECandidate.Runtime.AccessListLoopHeapIndependentOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual return preserves a distinct earlier transaction slice array. -/
theorem access_loop_returned_heap_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeRecords : watchedArray.toNat + watchedCount.toNat * 16 ≤ records.toNat)
    (valid : AccessHeapLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state accessLoopAndReturn = (some (.returned value),post)) :
    RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat := by
  obtain ⟨middle,loopRun,shape,restored⟩ := access_loop_returned_heap_result state post array count records input inputLength scratch frame
    ceiling inputLimit valid inputBound limitBound orderedFrame framePositive scratchBelow arrayAbove arrayBeforeRecords countLimit inputBeforeFrame budget value run
  obtain ⟨result,output,evaluated,_,_,_,done,_⟩ := evaluate_access_loop_heap_independent_outer_prefix_bounded state array count records input inputLength scratch frame
    ceiling inputLimit watchedArray watchedCount watchedInput watchedLength watchedValid watchedAbove watchedBeforeRecords valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayAbove arrayBeforeRecords countLimit inputBeforeFrame budget
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (evaluated.symm.trans loopRun)
  obtain ⟨next,_,retained⟩ := done rfl
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame output _ watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩

#print axioms access_loop_returned_heap_independent_outer_prefix
end InitECandidate.Runtime
