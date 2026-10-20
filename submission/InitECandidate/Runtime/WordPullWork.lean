import InitECandidate.Runtime.WordSelectionWork
import Flapjack.Compiler.Backend.WordInst.ExecutablePullExp
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordInst.ExecutablePullExp

theorem wordExpressionWork_positive (e : WordLangExpHOL (BitVec 64)) : 1 ≤ wordExpressionWork e := by
  cases e <;> simp only [wordExpressionWork] <;> omega

theorem wordExpressionsWork_append (left right : List (WordLangExpHOL (BitVec 64))) :
    wordExpressionsWork (left ++ right) = wordExpressionsWork left + wordExpressionsWork right := by
  induction left with
  | nil => simp [wordExpressionsWork]
  | cons head tail ih => simp [wordExpressionsWork, ih, Nat.add_assoc]

theorem wordExpressionsWork_length (es : List (WordLangExpHOL (BitVec 64))) :
    es.length ≤ wordExpressionsWork es := by
  induction es with
  | nil => simp [wordExpressionsWork]
  | cons head tail ih =>
    have positive := wordExpressionWork_positive head
    simp only [List.length_cons, wordExpressionsWork]
    omega

theorem partition_word_work (predicate : WordLangExpHOL (BitVec 64) → Bool)
    (es left right : List (WordLangExpHOL (BitVec 64))) :
    wordExpressionsWork (holPart predicate es left right).1 +
      wordExpressionsWork (holPart predicate es left right).2 =
      wordExpressionsWork es + wordExpressionsWork left + wordExpressionsWork right := by
  induction es generalizing left right with
  | nil => simp [holPart, wordExpressionsWork]
  | cons head tail ih =>
    simp only [holPart]
    split
    · have next := ih (head :: left) right
      simp only [wordExpressionsWork] at next ⊢
      omega
    · have next := ih left (head :: right)
      simp only [wordExpressionsWork] at next ⊢
      omega

theorem partition_word_work_total (predicate : WordLangExpHOL (BitVec 64) → Bool)
    (es : List (WordLangExpHOL (BitVec 64))) :
    wordExpressionsWork (holPartition predicate es).1 +
      wordExpressionsWork (holPartition predicate es).2 = wordExpressionsWork es := by
  simpa [holPartition, wordExpressionsWork] using partition_word_work predicate es [] []

theorem reduce_const_work (operator : BinOp) (value : BitVec 64)
    (rest : List (WordLangExpHOL (BitVec 64))) :
    wordExpressionWork (reduceConst operator value rest) ≤ 2 + wordExpressionsWork rest := by
  unfold reduceConst
  repeat' split
  all_goals simp_all [wordExpressionWork, wordExpressionsWork] <;> omega

theorem convert_sub_work (es : List (WordLangExpHOL (BitVec 64))) :
    wordExpressionWork (convertSub es) ≤ 1 + wordExpressionsWork es := by
  unfold convertSub
  repeat' split
  all_goals simp_all [wordExpressionWork, wordExpressionsWork] <;> omega

theorem optimize_non_sub_work (operator : BinOp) (notSub : operator ≠ .sub)
    (es : List (WordLangExpHOL (BitVec 64))) :
    wordExpressionWork (optimizeNonSub operator notSub es) ≤ 1 + wordExpressionsWork es := by
  have total := partition_word_work_total isConst es
  unfold optimizeNonSub
  rcases hp : holPartition isConst es with ⟨constants, variables⟩
  rw [hp] at total
  simp only [] at total
  cases constants with
  | nil =>
    dsimp only
    simp only [wordExpressionsWork, Nat.zero_add] at total
    simp only [wordExpressionWork]
    omega
  | cons head tail =>
    dsimp only
    have lower := wordExpressionsWork_length (head :: tail)
    have reduced := reduce_const_work operator (nonSubWordOp operator notSub
      ((head :: tail).map rmConst)) variables
    simp only [List.length_cons] at lower
    omega

theorem pull_ops_work (operator : BinOp) (es acc : List (WordLangExpHOL (BitVec 64))) :
    wordExpressionsWork (pullOps operator es acc) ≤ wordExpressionsWork es + wordExpressionsWork acc := by
  induction es generalizing acc with
  | nil => simp [pullOps, wordExpressionsWork]
  | cons head tail ih =>
    have regular := ih (head :: acc)
    cases head with
    | op childOp children =>
      simp only [pullOps]
      split
      · have flattened := ih (children ++ acc)
        rw [wordExpressionsWork_append] at flattened
        simp only [wordExpressionsWork, wordExpressionWork]
        omega
      · simp only [wordExpressionsWork] at regular ⊢
        exact Nat.le_trans regular (by omega)
    | _ =>
      simp only [pullOps]
      simp only [wordExpressionsWork] at regular ⊢
      omega

private theorem attach_pull_map (es : List (WordLangExpHOL (BitVec 64))) :
    (es.attach.map (fun pair => pullExpExecutable pair.1)) = es.map pullExpExecutable := by simp

mutual
  /-- Constant pulling and associative grouping do not increase expression work. -/
  theorem pull_executable_work (e : WordLangExpHOL (BitVec 64)) :
      wordExpressionWork (pullExpExecutable e) ≤ wordExpressionWork e := by
    cases e with
    | const value | var value | lookup value => simp [pullExpExecutable, wordExpressionWork]
    | load child =>
      have smaller := pull_executable_work child
      simp only [pullExpExecutable, wordExpressionWork]
      omega
    | shift operator left right =>
      have a := pull_executable_work left
      have b := pull_executable_work right
      simp only [pullExpExecutable, wordExpressionWork]
      omega
    | op operator args =>
      by_cases sub : operator = .sub
      · subst operator
        have children := pull_executables_work args
        have converted := convert_sub_work (args.map pullExpExecutable)
        simp only [pullExpExecutable, ↓reduceDIte, attach_pull_map, wordExpressionWork]
        omega
      · cases args with
        | nil =>
          simp [pullExpExecutable, sub, opConsts, wordExpressionWork, wordExpressionsWork]
          cases operator <;> simp [wordExpressionWork]
        | cons first tail =>
          cases tail with
          | nil =>
            have smaller := pull_executable_work first
            simp [pullExpExecutable, sub, wordExpressionWork, wordExpressionsWork]
            omega
          | cons second rest =>
            have children := pull_executables_work (first :: second :: rest)
            have pulled := pull_ops_work operator ((first :: second :: rest).map pullExpExecutable) []
            have optimized := optimize_non_sub_work operator sub
              (pullOps operator ((first :: second :: rest).map pullExpExecutable) [])
            simp only [wordExpressionsWork, Nat.add_zero] at pulled
            simp only [pullExpExecutable, sub, ↓reduceDIte, attach_pull_map, wordExpressionWork]
            omega
  termination_by sizeOf e
  decreasing_by all_goals (simp_wf; try omega)

  theorem pull_executables_work (es : List (WordLangExpHOL (BitVec 64))) :
      wordExpressionsWork (es.map pullExpExecutable) ≤ wordExpressionsWork es := by
    cases es with
    | nil => simp [wordExpressionsWork]
    | cons head tail =>
      have first := pull_executable_work head
      have rest := pull_executables_work tail
      simp only [List.map_cons, wordExpressionsWork]
      omega
  termination_by sizeOf es
  decreasing_by all_goals (simp_wf; try omega)
end

/-- Bound for the actual pinned selector's original constant-pulling function. -/
theorem pull_expression_work (e : WordLangExpHOL (BitVec 64)) :
    wordExpressionWork (pullExp e) ≤ wordExpressionWork e := by
  rw [← pullExpExecutable_eq]
  exact pull_executable_work e

/-- The complete pinned assignment selector, including constant pulling and
binary normalization, has a two-unit local expression-work bound. -/
theorem assignment_selection_work_bound (config : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64)
    (target temp : Nat) (expression : WordLangExpHOL (BitVec 64)) :
    selectionLeaves (instSelect config temp (.assign target expression)) + 1 ≤
      2 * wordExpressionWork expression := by
  have selected := flattened_selection_work_bound config target temp (pullExp expression)
  have pulled := pull_expression_work expression
  simp only [instSelect]
  omega

/-- Loop expressions retain the same small selector bound after their exact
Word expression lowering. This still counts emitted leaves, not native steps. -/
theorem loop_assignment_selection_work_bound
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64) (context : Spt Nat)
    (target temp : Nat) (expression : HolLoopExp 64) :
    selectionLeaves (instSelect config temp
      (.assign target (LoopToWord.compExpHOL context expression))) + 1 ≤
      2 * loopValueWork expression := by
  simpa only [loop_to_word_expression_work] using
    assignment_selection_work_bound config target temp (LoopToWord.compExpHOL context expression)

#print axioms assignment_selection_work_bound
#print axioms loop_assignment_selection_work_bound

#print axioms pull_expression_work

#print axioms reduce_const_work
#print axioms optimize_non_sub_work
#print axioms pull_ops_work
end InitECandidate.Runtime.FineCost
