import InitECandidate.Runtime.WordPermuteReturnAll

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

/-- Whole-program cost-aware permutation transport. Every recursive witness
preserves the same semantic execution and its pure-node cost; no restriction
on the function table, source locals or compiler pass is required. -/
theorem word_permute_executed_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) :
    PermuteCostGoal price program source := by
  cases program
  case seq first second =>
    apply permute_cost_seq price first second source
    · exact word_permute_executed_cost price first source
    · intro middle actual
      have clocks := evaluate_clock first source none middle actual
      exact word_permute_executed_cost price second middle
  case ite cmp reg operand first second =>
    exact permute_cost_ite price cmp reg operand first second source
      (word_permute_executed_cost price first source)
      (word_permute_executed_cost price second source)
  case mustTerminate body =>
    apply permute_cost_mustTerminate price body source
    intro positive
    exact word_permute_executed_cost price body
      {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
  case loop names body exits =>
    apply permute_cost_loop price names exits body source
    · intro cutSource cut
      have clocks := cutState_clock_termdep (names, .ln) source cutSource cut
      exact word_permute_executed_cost price body cutSource
    · intro cutSource result middle cut actual continuing positive
      have clocks := evaluate_clock body cutSource result middle actual
      have cutClocks := cutState_clock_termdep (names, .ln) source cutSource cut
      exact word_permute_executed_cost price (.loop names body exits) (decClock middle)
  case call returns destination arguments handler =>
    have calleeIH : PermuteClockIH price source := by
      intro child childSource smaller
      exact word_permute_executed_cost price child childSource
    rcases returns with _ | ⟨values, names, continuation, l1, l2⟩
    · rcases handler with _ | ⟨reg, handlerCode, h1, h2⟩
      · apply permute_cost_tail price destination arguments source
        intro xs actualArguments body size get found positive
        apply calleeIH body
        simp only [WordSemStateFiniteExact.callEnv, decClock]
        apply Prod.Lex.right
        omega
      · intro finalPermutation safe
        simp only [WordToWord.evaluate_call_eq] at safe
        repeat' split at safe
        all_goals exact (safe rfl).elim
    · exact permute_cost_return price values names continuation l1 l2 destination arguments handler source calleeIH
  all_goals
    apply permute_cost_atomic
    rfl
termination_by (source.termdep, source.clock, sizeOf program)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, decClock]
  all_goals omega

#print axioms word_permute_executed_cost
end InitECandidate.Runtime.FineCost
