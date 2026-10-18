import InitECandidate.Runtime.AuthorizationsLoopReturnIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsLoopHeapIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsLoopReturnHeapBound
import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsLoopHeapWitness
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem authorization_loop_returned_heap_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AuthorizationsHeapLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 16 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64) (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeRecords : watchedArray.toNat + watchedCount.toNat * 16 ≤ records.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state authorizationLoopAndReturn = (some (.returned value),post)) :
    RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat := by
  obtain ⟨result,middle,loopRun,_,_,_,done,noReturn⟩ := evaluate_authorizations_loop_independent_outer_prefix_heap_bounded state
    array count records input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayFits arrayAbove arrayBeforeRecords countLimit inputBeforeFrame watchedArray watchedCount watchedInput watchedLength watchedValid watchedFits watchedAbove watchedBeforeRecords budget
  rw [source_authorization_loop_and_return,evaluateHOLFiniteState_seq_line780,loopRun] at run
  cases result with
  | some result =>
    dsimp only at run
    have equal := (Prod.mk.inj run).1
    exact False.elim (noReturn value equal)
  | none =>
    dsimp only at run
    obtain ⟨next,_,retained⟩ := done rfl
    have memory := evaluate_readOnly_memory
      (.return (.rstruct [.var .local (ofString "recs"),.rfield 1 (.var .local (ofString "lst"))])) (by rfl) middle
    have metadata := evaluateHOLFiniteState_metadata middle
      (.return (.rstruct [.var .local (ofString "recs"),.rfield 1 (.var .local (ofString "lst"))]))
    rw [run] at memory metadata
    intro slot inside
    obtain ⟨p,n,item⟩ := retained slot inside
    exact ⟨p,n,item.after_frame middle post watchedArray slot p n watchedInput watchedLength metadata.2.1 (congrFun memory _) (congrFun memory _)⟩

#print axioms authorization_loop_returned_heap_independent_outer_prefix
end InitECandidate.Runtime
