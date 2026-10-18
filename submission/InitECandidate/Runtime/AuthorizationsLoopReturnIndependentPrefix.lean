import InitECandidate.Runtime.AuthorizationsLoopIndependentPrefix
import InitECandidate.Runtime.AuthorizationsLoopReturnBound
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem authorization_loop_returned_independent_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AuthorizationsLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 16 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (watchedArray watchedCount : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray input inputLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (watchedBeforeRecords : watchedArray.toNat + watchedCount.toNat * 16 ≤ records.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state authorizationLoopAndReturn = (some (.returned value),post)) :
    RlpSliceInputPrefix post watchedArray input inputLength watchedCount.toNat := by
  obtain ⟨result,middle,loopRun,_,_,_,done,noReturn⟩ := evaluate_authorizations_loop_independent_prefix_bounded state
    array count records input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayBeforeFrame arrayBeforeRecords countLimit inputBeforeFrame watchedArray watchedCount watchedValid watchedBeforeFrame watchedBeforeRecords budget
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
    exact ⟨p,n,item.after_frame middle post watchedArray slot p n input inputLength metadata.2.1 (congrFun memory _) (congrFun memory _)⟩

#print axioms authorization_loop_returned_independent_prefix
end InitECandidate.Runtime
