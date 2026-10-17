import InitECandidate.Runtime.RlpSlicesUpdatesInvariant
import InitECandidate.Runtime.NoLoopControlStores
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Actual slice iterations cannot bypass loop induction with callee
returns, break or continue; only normal progress or exceptional exit remains. -/
theorem evaluate_rlpSlices_step_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state rlpSlicesStep).1 ≠ some .break ∧
      (evaluateHOLFiniteState state rlpSlicesStep).1 ≠ some .continue ∧
      (∀ value, (evaluateHOLFiniteState state rlpSlicesStep).1 ≠ some (.returned value)) := by
  have noControl : noLoopControlStores rlpSlicesStep = true := by
    rw [source_rlpSlices_step,source_rlpSlices_updates,source_rlpSlices_advances]
    rfl
  have noReturn : noDirectReturn rlpSlicesStep = true := by
    rw [source_rlpSlices_step,source_rlpSlices_updates,source_rlpSlices_advances]
    rfl
  have control := evaluate_noLoopControlStores rlpSlicesStep noControl state
  exact ⟨control.1,control.2,fun value => evaluate_noDirectReturn rlpSlicesStep noReturn state value⟩

#print axioms evaluate_rlpSlices_step_control
end InitECandidate.Runtime
