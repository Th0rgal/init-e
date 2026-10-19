import InitECandidate.Runtime.NibbleScopedWordFrame
import InitECandidate.Runtime.KeyToNibblesStepFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem keyNibble_main_scopedWordFrame : NibbleScopedWordFrame 8 keyToNibblesMainStep := by
  simp only [keyToNibblesMainStep,keyToNibblesMainLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  exact (NibbleScopedWordFrame.declare _ _ (by decide) (by decide) (NibbleScopedWordFrame.store 0 _ (by decide) (NibbleScopedWordFrame.store 1 _ (by decide) (NibbleScopedWordFrame.declare _ _ (by decide) (by decide) (NibbleScopedWordFrame.store 2 _ (by decide) (NibbleScopedWordFrame.store 3 _ (by decide) (NibbleScopedWordFrame.declare _ _ (by decide) (by decide) (NibbleScopedWordFrame.store 4 _ (by decide) (NibbleScopedWordFrame.store 5 _ (by decide) (NibbleScopedWordFrame.declare _ _ (by decide) (by decide) (NibbleScopedWordFrame.store 6 _ (by decide) (NibbleScopedWordFrame.store 7 _ (by decide) (NibbleScopedWordFrame.tail _ rfl)))))))))))))

theorem keyNibble_tail_scopedWordFrame : NibbleScopedWordFrame 2 keyToNibblesTailStep := by
  simp only [keyToNibblesTailStep,keyToNibblesTailLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  exact (NibbleScopedWordFrame.declare _ _ (by decide) (by decide) (NibbleScopedWordFrame.store 0 _ (by decide) (NibbleScopedWordFrame.store 1 _ (by decide) (NibbleScopedWordFrame.tail _ rfl))))

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.keyNibble_main_scopedWordFrame
#print axioms InitECandidate.Runtime.keyNibble_tail_scopedWordFrame
