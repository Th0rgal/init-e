import InitECandidate.Runtime.WordOptimizerContextCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Whole unreachable-code normalization in an actual suffix context.
Recursion is structural in the source program; loop iteration and returning
call work are supplied by checked runtime congruence lemmas. -/
theorem optimizer_seqAssocRight_cost_le {C F : Type}
    (program suffix : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.seq program suffix) source).1 ≠ some .error) :
    wordExecutionCost wordOptimizerLocalPrice (WordUnreach.seqAssocRight program suffix) source ≤
      wordExecutionCost wordOptimizerLocalPrice (.seq program suffix) source := by
  cases program
  case skip =>
    simpa only [WordUnreach.seqAssocRight, optimizer_seq_skip_left_cost_eq] using
      (Nat.le_refl (wordExecutionCost wordOptimizerLocalPrice suffix source))
  case seq first second =>
    have reassociated : (evaluate (.seq first (.seq second suffix)) source).1 ≠ some .error := by
      rwa [WordUnreach.evaluateSeqAssoc]
    have childSafe : ∀ middle, evaluate first source = (none, middle) →
        (evaluate (.seq second suffix) middle).1 ≠ some .error := by
      intro middle actual
      rw [evaluate, fix_clock_evaluate, actual] at reassociated
      exact reassociated
    have same := optimizer_seq_suffix_run_eq first (.seq second suffix)
      (WordUnreach.seqAssocRight second suffix) source
      (fun middle actual => optimizer_seqAssocRight_run_eq second suffix middle (childSafe middle actual))
    have nextSafe : (evaluate (.seq first (WordUnreach.seqAssocRight second suffix)) source).1 ≠
        some .error := same.symm ▸ reassociated
    calc
      _ ≤ wordExecutionCost wordOptimizerLocalPrice
          (.seq first (WordUnreach.seqAssocRight second suffix)) source :=
        optimizer_seqAssocRight_cost_le first _ source nextSafe
      _ ≤ wordExecutionCost wordOptimizerLocalPrice (.seq first (.seq second suffix)) source :=
        optimizer_seq_suffix_cost_le first (.seq second suffix) _ source
          (fun middle actual => optimizer_seqAssocRight_cost_le second suffix middle (childSafe middle actual))
      _ = _ := (optimizer_seq_assoc_cost_eq first second suffix source).symm
  case ite cmp register operand first second =>
    apply optimizer_normalized_context_cost_le
      (.ite cmp register operand first second)
      (.ite cmp register operand (WordUnreach.removeUnreach first) (WordUnreach.removeUnreach second))
      suffix source rfl safe
    apply optimizer_if_body_cost_le _ _ _ _ _ _ _ source
      (optimizer_seq_prefix_safe _ _ source safe)
    · intro childSafe
      have h := optimizer_seqAssocRight_cost_le first .skip source
        (by rwa [WordUnreach.evaluateSeqSkip])
      simpa only [optimizer_seq_skip_right_cost_eq, WordUnreach.removeUnreach] using h
    · intro childSafe
      have h := optimizer_seqAssocRight_cost_le second .skip source
        (by rwa [WordUnreach.evaluateSeqSkip])
      simpa only [optimizer_seq_skip_right_cost_eq, WordUnreach.removeUnreach] using h
  case mustTerminate body =>
    apply optimizer_normalized_context_cost_le (.mustTerminate body)
      (.mustTerminate (WordUnreach.removeUnreach body)) suffix source rfl safe
    apply optimizer_mustTerminate_body_cost_le body _ source (optimizer_seq_prefix_safe _ _ source safe)
    intro child childSafe
    have h := optimizer_seqAssocRight_cost_le body .skip child
      (by rwa [WordUnreach.evaluateSeqSkip])
    simpa only [optimizer_seq_skip_right_cost_eq, WordUnreach.removeUnreach] using h
  case loop names body exits =>
    apply optimizer_normalized_context_cost_le (.loop names body exits)
      (.loop names (WordUnreach.removeUnreach body) exits) suffix source rfl safe
    apply optimizer_loop_body_cost_le names exits body _
      (fun child childSafe => optimizer_removeUnreach_run_eq body child childSafe) ?_ source
      (optimizer_seq_prefix_safe _ _ source safe)
    intro child childSafe
    have h := optimizer_seqAssocRight_cost_le body .skip child
      (by rwa [WordUnreach.evaluateSeqSkip])
    simpa only [optimizer_seq_skip_right_cost_eq, WordUnreach.removeUnreach] using h
  case call returns destination arguments handler =>
    cases returnsEq : returns with
    | none =>
      rw [returnsEq] at safe
      rw [optimizer_seq_stopped_cost_eq _ _ _ (optimizer_tail_call_stops destination arguments handler source)]
      exact Nat.le_refl _
    | some data =>
      rw [returnsEq] at safe
      rcases data with ⟨values, names, continuation, l1, l2⟩
      cases handlerEq : handler with
      | none =>
        rw [handlerEq] at safe
        apply optimizer_normalized_context_cost_le
          (.call (some (values, names, continuation, l1, l2)) destination arguments none)
          (.call (some (values, names, WordUnreach.removeUnreach continuation, l1, l2))
            destination arguments none) suffix source rfl safe
        apply optimizer_returning_none_continuation_cost_le _ _ _ _ _ _ _ _ source
          (optimizer_seq_prefix_safe _ _ source safe)
        intro child childSafe
        have h := optimizer_seqAssocRight_cost_le continuation .skip child
          (by rwa [WordUnreach.evaluateSeqSkip])
        simpa only [optimizer_seq_skip_right_cost_eq, WordUnreach.removeUnreach] using h
      | some data =>
        rw [handlerEq] at safe
        rcases data with ⟨register, handlerBody, h1, h2⟩
        apply optimizer_normalized_context_cost_le
          (.call (some (values, names, continuation, l1, l2)) destination arguments
            (some (register, handlerBody, h1, h2)))
          (.call (some (values, names, WordUnreach.removeUnreach continuation, l1, l2)) destination arguments
            (some (register, WordUnreach.removeUnreach handlerBody, h1, h2))) suffix source rfl safe
        apply optimizer_returning_handler_continuation_cost_le _ _ _ _ _ _ _ _ _ _ _ _ _ source
          (optimizer_seq_prefix_safe _ _ source safe)
        · intro child childSafe
          have h := optimizer_seqAssocRight_cost_le continuation .skip child
            (by rwa [WordUnreach.evaluateSeqSkip])
          simpa only [optimizer_seq_skip_right_cost_eq, WordUnreach.removeUnreach] using h
        · intro child childSafe
          have h := optimizer_seqAssocRight_cost_le handlerBody .skip child
            (by rwa [WordUnreach.evaluateSeqSkip])
          simpa only [optimizer_seq_skip_right_cost_eq, WordUnreach.removeUnreach] using h
  all_goals exact optimizer_simpSeq_cost_le _ suffix source safe
termination_by sizeOf program
decreasing_by
  all_goals try simp_all
  all_goals subst_vars
  all_goals try simp_all
  all_goals subst_vars
  all_goals try simp_all
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

/-- Semantic and executed-cost endpoint of the whole local removeUnreach
pass. No per-branch, callee, target-run or cost hypotheses remain. -/
theorem optimizer_removeUnreach_executed_correct {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate program source).1 ≠ some .error) :
    evaluate (WordUnreach.removeUnreach program) source = evaluate program source ∧
      wordExecutionCost wordOptimizerLocalPrice (WordUnreach.removeUnreach program) source ≤
        wordExecutionCost wordOptimizerLocalPrice program source := by
  refine ⟨optimizer_removeUnreach_run_eq program source safe, ?_⟩
  have h := optimizer_seqAssocRight_cost_le program .skip source
    (by rwa [WordUnreach.evaluateSeqSkip])
  simpa only [optimizer_seq_skip_right_cost_eq, WordUnreach.removeUnreach] using h

#print axioms optimizer_seqAssocRight_cost_le
#print axioms optimizer_removeUnreach_executed_correct
end InitECandidate.Runtime.FineCost
