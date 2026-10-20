import InitECandidate.Runtime.WordFlattenWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- Syntactic count of selected leaves. Only straight-line selector outputs
will be related to execution; this function alone is not a loop/call bound. -/
def selectionLeaves : WordLangProgHOL (BitVec 64) → Nat
  | .skip => 0
  | .seq first second => selectionLeaves first + selectionLeaves second
  | .move _ moves => moves.length
  | _ => 1
termination_by p => sizeOf p

/-- The raw selector emits no more leaves than the input expression's local
node work. Constant/immediate/address-offset shortcuts only reduce this count. -/
theorem raw_selection_work_bound (config : AsmConfigExact 64) (target temp : Nat)
    (expression : WordLangExpHOL (BitVec 64)) :
    selectionLeaves (instSelectExp config target temp expression) ≤ wordExpressionWork expression := by
  cases expression with
  | const value | var value | lookup value => simp [instSelectExp, selectionLeaves, wordExpressionWork]
  | load address =>
    have addressBound := raw_selection_work_bound config temp temp address
    rw [instSelectExp.eq_def]
    dsimp only
    split
    · rename_i child offset
      split
      · have childBound := raw_selection_work_bound config temp temp child
        simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork]
        omega
      · have childBound := raw_selection_work_bound config temp temp
          (.op .add [child, .const offset])
        simp only [wordExpressionWork, wordExpressionsWork] at childBound
        simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork]
        omega
    · simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork]
      omega
  | op operator args =>
    cases args with
    | nil => simp [instSelectExp, selectionLeaves, wordExpressionWork]
    | cons first tail =>
      cases tail with
      | nil => simp [instSelectExp, selectionLeaves, wordExpressionWork]
      | cons second tail =>
        cases tail with
        | cons third rest => simp [instSelectExp, selectionLeaves, wordExpressionWork]
        | nil =>
          rw [instSelectExp]
          split
          · have firstBound := raw_selection_work_bound config temp temp first
            simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork]
            omega
          · split
            · have secondBound := raw_selection_work_bound config temp temp second
              simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork]
              omega
            · have firstBound := raw_selection_work_bound config temp temp first
              have secondBound := raw_selection_work_bound config (temp+1) (temp+1) second
              split
              · rename_i value
                split
                · simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork]; omega
                · split <;> simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork] <;> omega
              · simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork]
                omega
  | shift operator operand amount =>
    have operandBound := raw_selection_work_bound config temp temp operand
    have amountBound := raw_selection_work_bound config (temp+1) (temp+1) amount
    rw [instSelectExp.eq_def]
    dsimp only
    split
    · rename_i value
      split
      · split <;> simp only [selectionLeaves, wordExpressionWork, List.length_cons, List.length_nil] <;> omega
      · simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork]; omega
    · simp only [selectionLeaves, wordExpressionWork, wordExpressionsWork]
      omega
termination_by sizeOf expression
  decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- Normalization followed by raw instruction selection has a small local
bound. Constant pulling precedes this expression in the full selector and
still needs its own nonamplification proof. -/
theorem flattened_selection_work_bound (config : AsmConfigExact 64) (target temp : Nat)
    (expression : WordLangExpHOL (BitVec 64)) :
    selectionLeaves (instSelectExp config target temp (flattenExp expression)) + 1 ≤
      2 * wordExpressionWork expression := by
  have selected := raw_selection_work_bound config target temp (flattenExp expression)
  have flattened := flatten_expression_work expression
  omega

#print axioms flattened_selection_work_bound

#print axioms raw_selection_work_bound
end InitECandidate.Runtime.FineCost
