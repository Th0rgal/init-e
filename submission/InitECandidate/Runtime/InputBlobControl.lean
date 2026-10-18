import InitECandidate.Runtime.InputBlobStep
import InitECandidate.Runtime.NoLoopControlWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A copy iteration cannot itself return or emit loop control, even when
the host terminates a shared-memory read. -/
theorem evaluate_inputBlob_step_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state inputBlobStep).1 ≠ some .break ∧
      (evaluateHOLFiniteState state inputBlobStep).1 ≠ some .continue ∧
      ∀ value, (evaluateHOLFiniteState state inputBlobStep).1 ≠ some (.returned value) := by
  have control := (evaluate_shared_load_control_frame state .opW (ofString "w")
    (.op .add [.const 1073741840,.var .local (ofString "i")])).2.1
  change (evaluateHOLFiniteState state inputBlobLoad).1 = none ∨
    (evaluateHOLFiniteState state inputBlobLoad).1 = some .error ∨
    ∃ event, (evaluateHOLFiniteState state inputBlobLoad).1 = some (.finalFfi event) at control
  rw [inputBlobStep,evaluateHOLFiniteState_seq_line780]
  cases loaded : evaluateHOLFiniteState state inputBlobLoad with
  | mk result next =>
    rw [loaded] at control
    rcases control with rfl | rfl | ⟨event,rfl⟩
    · have tail := evaluate_noLoopControlWhile
        (.seq (.store (.op .add [.var .local (ofString "p"),.var .local (ofString "i")])
          (.var .local (ofString "w")))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 8]))) (by rfl) next
      exact ⟨tail.1,tail.2,fun value => evaluate_noDirectReturnWhile _ (by rfl) next value⟩
    · simp
    · simp

theorem evaluate_inputBlob_loop_no_return {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state inputBlobLoop).1 ≠ some (.returned value) :=
  (evaluate_while_terminal_control inputBlobCondition inputBlobStep
    (fun current => (evaluate_inputBlob_step_control current).2.2) state).2.2 value

#print axioms evaluate_inputBlob_step_control
#print axioms evaluate_inputBlob_loop_no_return
end InitECandidate.Runtime
