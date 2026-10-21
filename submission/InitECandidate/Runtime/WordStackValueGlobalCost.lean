import InitECandidate.Runtime.WordStackValueReturnAll

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

/-- Whole-program executed-cost transport across value-equal saved stacks.
SSA may rename saved-frame keys. The actual run's cost is preserved under
that substitution, including all callee/handler/continuation executions.
No allocation/install restriction or whole-code-table budget is assumed. -/
theorem word_stack_value_executed_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) :
    StackValueCostGoal price program source := by
  cases program
  case seq first second =>
    apply stack_value_cost_seq price first second source
    · exact word_stack_value_executed_cost price first source
    · intro middle actual
      have clocks := evaluate_clock first source none middle actual
      exact word_stack_value_executed_cost price second middle
  case ite cmp reg operand first second =>
    exact stack_value_cost_ite price cmp reg operand first second source
      (word_stack_value_executed_cost price first source)
      (word_stack_value_executed_cost price second source)
  case mustTerminate body =>
    apply stack_value_cost_mustTerminate price body source
    intro positive
    exact word_stack_value_executed_cost price body
      {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
  case loop names body exits =>
    apply stack_value_cost_loop price names exits body source
    · intro cutSource cut
      have clocks := cutState_clock_termdep (names, .ln) source cutSource cut
      exact word_stack_value_executed_cost price body cutSource
    · intro cutSource result middle cut actual continuing positive
      have clocks := evaluate_clock body cutSource result middle actual
      have cutClocks := cutState_clock_termdep (names, .ln) source cutSource cut
      exact word_stack_value_executed_cost price (.loop names body exits) (decClock middle)
  case call returns destination arguments handler =>
    have calleeIH : StackValueClockIH price source := by
      intro child childSource smaller
      exact word_stack_value_executed_cost price child childSource
    rcases returns with _ | ⟨values, names, continuation, l1, l2⟩
    · rcases handler with _ | ⟨reg, handlerCode, h1, h2⟩
      · apply stack_value_cost_tail price destination arguments source
        intro xs actualArguments body size get found positive
        apply calleeIH body
        simp only [WordSemStateFiniteExact.callEnv, decClock]
        apply Prod.Lex.right
        omega
      · intro safe stack related
        simp only [WordToWord.evaluate_call_eq] at safe
        repeat' split at safe
        all_goals exact (safe rfl).elim
    · exact stack_value_cost_return price values names continuation l1 l2 destination arguments handler source calleeIH
  all_goals
    apply stack_value_cost_atomic
    rfl
termination_by (source.termdep, source.clock, sizeOf program)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, decClock]
  all_goals omega

/-- State-independent local prices may be supplied in their usual binary
form. This specializes the pure-price result without changing the program,
actual source run, code table or stack metadata. -/
theorem word_execution_cost_stack_value_invariant {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (independent : ∀ p a b, price p a = price p b)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (stack : List (WordSemStackFrame 64))
    (safe : (evaluate program source).1 ≠ some .error)
    (related : Flapjack.WordSemStackEq.sValEq source.stack stack) :
    wordExecutionCost price program {source with stack := stack} = wordExecutionCost price program source := by
  let pure : WordLangProgHOL (BitVec 64) → Nat := fun p => price p source
  have prices : price = (fun p _ => pure p) := by
    funext p state
    exact independent p state source
  rw [prices]
  exact word_stack_value_executed_cost pure program source safe stack related

#print axioms word_stack_value_executed_cost
#print axioms word_execution_cost_stack_value_invariant
end InitECandidate.Runtime.FineCost
