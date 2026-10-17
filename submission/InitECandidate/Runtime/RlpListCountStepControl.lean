import InitECandidate.Runtime.RlpListCountStep
import InitECandidate.Runtime.NoLoopControlStores
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Actual list-count iterations cannot bypass loop induction with callee
returns, break or continue; only normal progress or exceptional exit remains. -/
theorem evaluate_rlpListCount_step_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state rlpListCountStep).1 ≠ some .break ∧
      (evaluateHOLFiniteState state rlpListCountStep).1 ≠ some .continue ∧
      (∀ value, (evaluateHOLFiniteState state rlpListCountStep).1 ≠ some (.returned value)) := by
  have noControl : noLoopControlStores rlpListCountStep = true := by
    rw [source_rlpListCount_step,source_rlpListCount_updates]
    rfl
  have noReturn : noDirectReturn rlpListCountStep = true := by
    rw [source_rlpListCount_step,source_rlpListCount_updates]
    rfl
  have control := evaluate_noLoopControlStores rlpListCountStep noControl state
  exact ⟨control.1,control.2,fun value => evaluate_noDirectReturn rlpListCountStep noReturn state value⟩

#print axioms evaluate_rlpListCount_step_control
end InitECandidate.Runtime
