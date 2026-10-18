import InitECandidate.Runtime.AuthorizationsLoopReturnBound
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem authorization_loop_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AuthorizationsLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 16 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state authorizationLoopAndReturn = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  obtain ⟨result,middle,loopRun,_,_,_,done,noReturn⟩ := evaluate_authorizations_loop_bounded state
    array count records input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayBeforeFrame arrayBeforeRecords countLimit inputBeforeFrame budget
  rw [source_authorization_loop_and_return,evaluateHOLFiniteState_seq_line780,loopRun] at run
  cases result with
  | some result =>
    dsimp only at run
    have equal := (Prod.mk.inj run).1
    exact False.elim (noReturn value equal)
  | none =>
    dsimp only at run
    obtain ⟨next,_⟩ := done rfl
    have globals : ∀ watched, post.globals.lookup watched = middle.globals.lookup watched := by
      intro watched
      have retained := evaluate_avoidsGlobalAssignment watched
        (.return (.rstruct [.var .local (ofString "recs"),.rfield 1 (.var .local (ofString "lst"))])) (by rfl) middle
      rw [run] at retained
      exact retained
    exact ⟨(globals _).trans next.scratchGlobal,(globals _).trans next.frameGlobal⟩

#print axioms authorization_loop_returned_globals
end InitECandidate.Runtime
