import InitECandidate.Runtime.RlpErrorCheck
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpErrorChecks (checks : List (ExpHOL 64 × BitVec 64)) (continuation : ProgHOL 64) : ProgHOL 64 :=
  checks.foldr (fun check rest => .seq
    (.ite check.1 (.call (some (none,none)) (ofString "rlp_fail") [.const check.2]) .skip) rest) continuation

/-- A sequence of original RLP checks either executes its continuation in
exactly the initial state or exits after at most one error-call tick. -/
theorem evaluate_rlp_error_checks {F : Type} (state : PanSemStateFiniteExact 64 F)
    (checks : List (ExpHOL 64 × BitVec 64)) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (rlpErrorChecks checks continuation) = (result,post) ∧
      (evaluateHOLFiniteState state continuation = (result,post) ∨
        (state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
          (∀ value, result ≠ some (.returned value)) ∧ post.memory = state.memory ∧ post.globals = state.globals)) := by
  induction checks with
  | nil =>
    cases run : evaluateHOLFiniteState state continuation with
    | mk result post => exact ⟨result,post,run,Or.inl rfl⟩
  | cons check rest ih =>
    obtain ⟨result,post,run,cost,remaining,noTimeout,normal,noReturn,memory,globals⟩ :=
      evaluate_rlp_error_check state check.1 check.2 code ticks
    change ∃ result post, evaluateHOLFiniteState state (.seq
      (.ite check.1 (.call (some (none,none)) (ofString "rlp_fail") [.const check.2]) .skip)
      (rlpErrorChecks rest continuation)) = (result,post) ∧ _
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      have same := normal rfl
      subst post
      exact ih
    | some stopped =>
      exact ⟨some stopped,post,rfl,Or.inr ⟨cost,remaining,noTimeout,by simp,noReturn,memory,globals⟩⟩

#print axioms evaluate_rlp_error_checks
end InitECandidate.Runtime
