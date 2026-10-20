import InitECandidate.Runtime.LoopToWordExpressionWork
import Flapjack.Compiler.Backend.WordInst
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordInst

mutual
  /-- Binary normalization has a two-unit node bound with one unit of
  potential. The potential prevents multiplying another bound at every child. -/
  theorem flatten_expression_work (e : WordLangExpHOL (BitVec 64)) :
      wordExpressionWork (flattenExp e) + 1 ≤ 2 * wordExpressionWork e := by
    cases e with
    | const value | var value | lookup value => simp [flattenExp, wordExpressionWork]
    | load child =>
      have smaller := flatten_expression_work child
      simp only [flattenExp, wordExpressionWork]
      omega
    | shift operator left right =>
      have a := flatten_expression_work left
      have b := flatten_expression_work right
      simp only [flattenExp, wordExpressionWork]
      omega
    | op operator args =>
      by_cases sub : operator = .sub
      · subst operator
        have children := flatten_expressions_work args
        simp only [flattenExp, wordExpressionWork]
        simpa using (show 1 + wordExpressionsWork (args.map flattenExp) + 1 ≤
          2 * (1 + wordExpressionsWork args) by omega)
      · cases args with
        | nil =>
          cases operator <;> simp [flattenExp, opConsts, wordExpressionWork, wordExpressionsWork] at *
        | cons head tail =>
          cases tail with
          | nil =>
            have smaller := flatten_expression_work head
            simp [flattenExp, sub, wordExpressionWork, wordExpressionsWork]
            omega
          | cons second tail =>
            have first := flatten_expression_work head
            have rest := flatten_expression_work (.op operator (second :: tail))
            simp only [wordExpressionWork, wordExpressionsWork] at rest
            simp only [flattenExp, sub, wordExpressionWork, wordExpressionsWork]
            omega
  termination_by sizeOf e
  decreasing_by all_goals (simp_wf; try omega)

  theorem flatten_expressions_work (es : List (WordLangExpHOL (BitVec 64))) :
      wordExpressionsWork (es.map flattenExp) + es.length ≤ 2 * wordExpressionsWork es := by
    cases es with
    | nil => simp [wordExpressionsWork]
    | cons head tail =>
      have first := flatten_expression_work head
      have rest := flatten_expressions_work tail
      simp only [List.map_cons, List.length_cons, wordExpressionsWork]
      omega
  termination_by sizeOf es
  decreasing_by all_goals (simp_wf; try omega)
end

#print axioms flatten_expression_work
#print axioms flatten_expressions_work
end InitECandidate.Runtime.FineCost
