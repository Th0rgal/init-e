import InitECandidate.Runtime.WordFunctionPermuteReturnAll

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

/-- Whole-program cost-aware permutation transport. Every recursive witness
preserves the same semantic execution and its pure-node cost; no restriction
on the function table, source locals or compiler pass is required. -/
theorem word_function_permute_executed_cost {C F : Type}
    (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) :
    FunctionPermuteCostGoal price function program source := by
  cases program
  case seq first second =>
    apply function_permute_cost_seq price function first second source
    · exact word_function_permute_executed_cost price function first source
    · intro middle actual
      have clocks := evaluate_clock first source none middle actual
      exact word_function_permute_executed_cost price function second middle
  case ite cmp reg operand first second =>
    exact function_permute_cost_ite price function cmp reg operand first second source
      (word_function_permute_executed_cost price function first source)
      (word_function_permute_executed_cost price function second source)
  case mustTerminate body =>
    apply function_permute_cost_mustTerminate price function body source
    intro positive
    exact word_function_permute_executed_cost price function body
      {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
  case loop names body exits =>
    apply function_permute_cost_loop price function names exits body source
    · intro cutSource cut
      have clocks := cutState_clock_termdep (names, .ln) source cutSource cut
      exact word_function_permute_executed_cost price function body cutSource
    · intro cutSource result middle cut actual continuing positive
      have clocks := evaluate_clock body cutSource result middle actual
      have cutClocks := cutState_clock_termdep (names, .ln) source cutSource cut
      exact word_function_permute_executed_cost price function (.loop names body exits) (decClock middle)
  case call returns destination arguments handler =>
    have calleeIH : FunctionPermuteClockIH price source := by
      intro childFunction child childSource smaller
      exact word_function_permute_executed_cost price childFunction child childSource
    rcases returns with _ | ⟨values, names, continuation, l1, l2⟩
    · rcases handler with _ | ⟨reg, handlerCode, h1, h2⟩
      · apply function_permute_cost_tail price function destination arguments source
        intro xs actualArguments body size get found positive
        apply calleeIH ((wordCallLabel destination xs).getD 0) body
        simp only [WordSemStateFiniteExact.callEnv, decClock]
        apply Prod.Lex.right
        omega
      · intro finalPermutation safe
        simp only [WordToWord.evaluate_call_eq] at safe
        repeat' split at safe
        all_goals exact (safe rfl).elim
    · exact function_permute_cost_return price function values names continuation l1 l2 destination arguments handler source calleeIH
  all_goals
    apply function_permute_cost_atomic
    rfl
termination_by (source.termdep, source.clock, sizeOf program)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, decClock]
  all_goals omega

#print axioms word_function_permute_executed_cost
end InitECandidate.Runtime.FineCost
