import InitECandidate.Runtime.ValidateHeadersFirstLoopReach
import InitECandidate.Runtime.ValidateHeadersFirstWindowLoop
import InitECandidate.Runtime.NoDirectReturnWhile
import InitECandidate.Runtime.RunBoundedSeqReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 300000

/-- The real normal loop exit preserves the initial heap lower bound. -/
theorem validate_headers_first_window_loop_normal {F : Type} (e : ValidateHeadersFirstEnvironment)
    (memory : BitVec 64 → HolWordLab 64) (s post : PanSemStateFiniteExact 64 F) (rank : Nat) (code : s.code = originalRuntimeCode)
    (valid : ValidateHeadersFirstWindowInvariant e memory s rank)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock)
    (normal : evaluateHOLFiniteState s (.while validateHeadersFirstCondition validateHeadersFirstBody) = (none,post)) :
    ValidateHeadersFirstWindowInvariant e memory post 0 ∧ post.code = s.code := by
  have exhausted := validate_headers_first_loop_normal e s post rank code valid.1.1 budget normal
  have small := Nat.mul_le_mul_right (validateHeadersFirstIterationCost e.inputLimit + 1)
    (validate_headers_first_invariant_rank_bound e s rank valid.1.1)
  have result := validate_headers_first_window_loop_ranked e memory rank s code valid (le_trans small budget)
  rw [normal] at result
  obtain ⟨m,kept,_,_⟩ := result.2.2.2 rfl
  exact ⟨⟨⟨exhausted.1,kept.1.2⟩,kept.2⟩,exhausted.2⟩

/-- The exact first-loop continuation is reached with monotone heap geometry,
or evaluation terminates within the existing uniform budget. -/
theorem validate_headers_first_window_loop_reaches {F : Type} (e : ValidateHeadersFirstEnvironment)
    (memory : BitVec 64 → HolWordLab 64) (s : PanSemStateFiniteExact 64 F) (rank : Nat) (code : s.code = originalRuntimeCode)
    (valid : ValidateHeadersFirstWindowInvariant e memory s rank)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock) :
    Reaches s (validateHeadersAt 4) (fun post => ValidateHeadersFirstWindowInvariant e memory post 0 ∧ post.code = s.code)
      (validateHeadersFirstLoopCost e.inputLimit) (validateHeadersAt 5) := by
  rw [source_validate_headers_first_loop]
  apply runBounded_seq_reaches s _ _ _ _ (runBounded_validate_headers_first_loop e s rank code valid.1.1 budget)
  · intro value
    apply evaluate_noDirectReturnWhile
    change noDirectReturnWhile validateHeadersFirstBody = true
    rw [source_validate_headers_first_decode]
    change noDirectReturnWhile validateHeadersFirstTail = true
    rw [source_validate_headers_first_tail]
    rfl
  · intro post normal
    exact validate_headers_first_window_loop_normal e memory s post rank code valid budget normal

#print axioms validate_headers_first_window_loop_normal
#print axioms validate_headers_first_window_loop_reaches
end InitECandidate.Runtime
