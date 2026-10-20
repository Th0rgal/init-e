import InitECandidate.Runtime.WordExecutionCostProps
import InitECandidate.Runtime.LoopToWordCodeWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- A supported local code allowance bounds the actual reached execution,
including early stops and either selected conditional branch. -/
theorem word_expression_code_executed {C F : Type}
    (p : WordLangProgHOL (BitVec 64)) (cost : Nat)
    (supported : wordExpressionCodeWork p = some cost)
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordLogicalPrice p s ≤ cost := by
  cases p with
  | skip => simpa [wordExpressionCodeWork, wordExecutionCost, wordLogicalPrice] using supported
  | assign name value =>
    simp only [wordExpressionCodeWork, Option.some.injEq] at supported
    simp [wordExecutionCost, wordLogicalPrice, ← supported]
  | inst instruction =>
    simp only [wordExpressionCodeWork, Option.some.injEq] at supported
    simp [wordExecutionCost, wordLogicalPrice, ← supported]
  | tick =>
    simp only [wordExpressionCodeWork, Option.some.injEq] at supported
    simp [wordExecutionCost, wordLogicalPrice, ← supported]
  | seq first second =>
    cases ha : wordExpressionCodeWork first with
    | none => simp [wordExpressionCodeWork, ha] at supported
    | some a =>
      cases hb : wordExpressionCodeWork second with
      | none => simp [wordExpressionCodeWork, ha, hb] at supported
      | some b =>
        have hc : a + b = cost := by simpa [wordExpressionCodeWork, ha, hb] using supported
        rw [wordLogicalCost_seq, ← hc]
        have ia := word_expression_code_executed first a ha s
        cases run : evaluate first s with
        | mk result middle =>
          cases result <;> simp only
          · have ib := word_expression_code_executed second b hb middle
            omega
          · omega
  | ite cmp reg operand yes no =>
    cases ha : wordExpressionCodeWork yes with
    | none => simp [wordExpressionCodeWork, ha] at supported
    | some a =>
      cases hb : wordExpressionCodeWork no with
      | none => simp [wordExpressionCodeWork, ha, hb] at supported
      | some b =>
        have hc : 1 + max a b = cost := by simpa [wordExpressionCodeWork, ha, hb] using supported
        have ia := word_expression_code_executed yes a ha s
        have ib := word_expression_code_executed no b hb s
        simp only [wordExecutionCost, wordLogicalPrice]
        split <;> (try simp_all)
        all_goals try (split <;> (try simp_all))
        all_goals omega
  | _ => simp [wordExpressionCodeWork] at supported
termination_by sizeOf p

/-- The existing Loop-to-Word local compiler certificate now bounds actual
Word execution, for every entry state, rather than just generated syntax. -/
theorem loop_to_word_executed_local {C F : Type}
    (context : Spt Nat) (p : HolLoopProg 64) (labels : Nat × Nat)
    (cost : Nat) (supported : loopExpressionCodeWork p = some cost)
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordLogicalPrice (LoopToWord.compHOL context p labels).1 s ≤ cost :=
  word_expression_code_executed _ cost
    (loop_to_word_code_work context p labels cost supported) s

#print axioms loop_to_word_executed_local
#print axioms word_expression_code_executed
end InitECandidate.Runtime.FineCost
