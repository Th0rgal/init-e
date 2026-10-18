import InitECandidate.Runtime.U256FromBeSource
import InitECandidate.Runtime.NormalLocalIncrement
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem u256FromBe_step_increments : NormalLocalIncrement (ofString "i") u256FromBeStep := by
  simp only [u256FromBeStep,u256FromBeLoop,u256FromBeLoopAndReturn,u256FromBeInitialized,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  apply normalLocalIncrement_dec _ _ _ _ _ (by decide)
  apply normalLocalIncrement_dec _ _ _ _ _ (by decide)
  apply normalLocalIncrement_dec _ _ _ _ _ (by decide)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  exact normalLocalIncrement_assign _

theorem u256FromBe_step_pointer_frame : straightLocalFrame (ofString "p") u256FromBeStep = true := by
  simp only [u256FromBeStep,u256FromBeLoop,u256FromBeLoopAndReturn,u256FromBeInitialized,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem u256FromBe_step_length_frame : straightLocalFrame (ofString "n") u256FromBeStep = true := by
  simp only [u256FromBeStep,u256FromBeLoop,u256FromBeLoopAndReturn,u256FromBeInitialized,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Every normally completed byte iteration advances once and retains the
original input pointer and byte count; no accumulator typing premise is needed. -/
theorem evaluate_u256FromBe_step_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state u256FromBeStep = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.locals.lookup (ofString "p") = state.locals.lookup (ofString "p") ∧
      post.locals.lookup (ofString "n") = state.locals.lookup (ofString "n") := by
  have pointer := evaluate_straight_local_frame (ofString "p") u256FromBeStep u256FromBe_step_pointer_frame state
  have length := evaluate_straight_local_frame (ofString "n") u256FromBeStep u256FromBe_step_length_frame state
  rw [run] at pointer length
  exact ⟨u256FromBe_step_increments state post index binding run,pointer,length⟩

#print axioms evaluate_u256FromBe_step_progress
end InitECandidate.Runtime
