import InitECandidate.Runtime.ValidateHeadersFirstUniformBound
import InitECandidate.Runtime.NoDirectReturnWhile
import InitECandidate.Runtime.RunBoundedSeqReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 300000

/-- Normal completion of the actual loop exhausts its rank and retains the
concrete real-table/heap/workspace invariant for the following code. -/
theorem validate_headers_first_loop_normal {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s post : PanSemStateFiniteExact 64 F) (rank : Nat) (code : s.code = originalRuntimeCode)
    (valid : ValidateHeadersFirstInvariant e s rank)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock)
    (normal : evaluateHOLFiniteState s (.while validateHeadersFirstCondition validateHeadersFirstBody) = (none,post)) :
    ValidateHeadersFirstInvariant e post 0 ∧ post.code = s.code := by
  have small := Nat.mul_le_mul_right (validateHeadersFirstIterationCost e.inputLimit + 1)
    (validate_headers_first_invariant_rank_bound e s rank valid)
  have result := validate_headers_first_loop_ranked e rank s code valid (by exact le_trans small budget)
  rw [normal] at result
  obtain ⟨m,next,installed,zero | impossible⟩ := result.2.2.2 rfl
  · obtain ⟨index,heap,arr,n,i,hs,hashes,within,distance,rest⟩ := next
    have ev := eval_validate_headers_first_condition post index e.count e.cap within i n
    rw [ev] at zero
    have outside : ¬ index.toNat < e.count.toNat := by
      intro inside
      simp [inside] at zero
    have rankZero : m = 0 := by omega
    subst m
    exact ⟨⟨index,heap,arr,n,i,hs,hashes,within,(by omega),rest⟩,installed⟩
  · exact impossible.elim

/-- The real source continuation after the first while is reached with its
exhausted invariant, or evaluation terminates within the uniform budget. -/
theorem validate_headers_first_loop_reaches {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) (code : s.code = originalRuntimeCode)
    (valid : ValidateHeadersFirstInvariant e s rank)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock) :
    Reaches s (validateHeadersAt 4) (fun post => ValidateHeadersFirstInvariant e post 0 ∧ post.code = s.code)
      (validateHeadersFirstLoopCost e.inputLimit) (validateHeadersAt 5) := by
  rw [source_validate_headers_first_loop]
  apply runBounded_seq_reaches s _ _ _ _ (runBounded_validate_headers_first_loop e s rank code valid budget)
  · intro value
    apply evaluate_noDirectReturnWhile
    change noDirectReturnWhile validateHeadersFirstBody = true
    rw [source_validate_headers_first_decode]
    change noDirectReturnWhile validateHeadersFirstTail = true
    rw [source_validate_headers_first_tail]
    rfl
  · intro post normal
    exact validate_headers_first_loop_normal e s post rank code valid budget normal

#print axioms validate_headers_first_loop_normal
#print axioms validate_headers_first_loop_reaches
end InitECandidate.Runtime
