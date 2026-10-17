import InitECandidate.Runtime.KeyToNibblesSyntax
import InitECandidate.Runtime.ByteAdvanceStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem keyToNibbles_main_step_advances : ByteAdvanceStep (ofString "i") 4 keyToNibblesMainStep := by
  simp only [keyToNibblesMainStep,keyToNibblesMainLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first | exact ByteAdvanceStep.advance | apply ByteAdvanceStep.store | apply ByteAdvanceStep.declare | decide

theorem keyToNibbles_tail_step_advances : ByteAdvanceStep (ofString "i") 1 keyToNibblesTailStep := by
  simp only [keyToNibblesTailStep,keyToNibblesTailLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first | exact ByteAdvanceStep.advance | apply ByteAdvanceStep.store | apply ByteAdvanceStep.declare | decide

/-- The original four-byte conversion step advances i by four if successful;
all byte failures exit with error and all other locals are restored. -/
theorem evaluate_keyToNibbles_main_step_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state keyToNibblesMainStep = (result,post) ∧ post.clock = state.clock ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 4)))) ∨ result = some .error) :=
  evaluate_byteAdvanceStep keyToNibbles_main_step_advances state index binding

/-- The original single-byte tail step has the same control frame and advances
its counter by one. -/
theorem evaluate_keyToNibbles_tail_step_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state keyToNibblesTailStep = (result,post) ∧ post.clock = state.clock ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 1)))) ∨ result = some .error) :=
  evaluate_byteAdvanceStep keyToNibbles_tail_step_advances state index binding

#print axioms keyToNibbles_main_step_advances
#print axioms keyToNibbles_tail_step_advances
#print axioms evaluate_keyToNibbles_main_step_frame
#print axioms evaluate_keyToNibbles_tail_step_frame
end InitECandidate.Runtime
