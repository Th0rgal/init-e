import InitECandidate.Runtime.BlobHashesSource
import InitECandidate.Runtime.NoLoopControlStores
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Callee returns cannot bypass blob iteration control or loop induction. -/
theorem evaluate_blobHashes_step_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state blobHashesStep).1 ≠ some .break ∧
      (evaluateHOLFiniteState state blobHashesStep).1 ≠ some .continue ∧
      (∀ value, (evaluateHOLFiniteState state blobHashesStep).1 ≠ some (.returned value)) := by
  have noControl : noLoopControlStores blobHashesStep = true := by
    rw [source_blobHashes_step]; rfl
  have noReturn : noDirectReturn blobHashesStep = true := by
    rw [source_blobHashes_step]; rfl
  have control := evaluate_noLoopControlStores blobHashesStep noControl state
  exact ⟨control.1,control.2,fun value => evaluate_noDirectReturn blobHashesStep noReturn state value⟩

#print axioms evaluate_blobHashes_step_control
end InitECandidate.Runtime
