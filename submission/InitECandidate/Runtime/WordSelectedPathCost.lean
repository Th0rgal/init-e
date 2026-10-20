import InitECandidate.Runtime.WordSelectionStraightLine
import InitECandidate.Runtime.WordPathWorkControl
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

theorem selection_leaves_positive (p : WordLangProgHOL (BitVec 64))
    (supported : selectionStraightLine p = true) : 1 ≤ selectionLeaves p := by
  cases p <;> simp only [selectionStraightLine, selectionLeaves, Bool.and_eq_true,
    decide_eq_true_eq] at *
  all_goals try contradiction
  all_goals try omega
  case seq first second =>
    have firstBound := selection_leaves_positive first supported.1
    omega
termination_by sizeOf p

theorem selection_path_work_bound {C F : Type}
    (p : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (supported : selectionStraightLine p = true) :
    wordPathWork p source + 1 ≤ 2 * selectionLeaves p := by
  cases p <;> simp only [selectionStraightLine, Bool.and_eq_true,
    decide_eq_true_eq] at supported <;> try contradiction
  all_goals try (simp only [wordPathWork, selectionLeaves]; omega)
  rename_i first second
  have firstBound := selection_path_work_bound first source supported.1
  have secondPositive := selection_leaves_positive second supported.2
  rw [wordPathWork_seq]
  simp only [selectionLeaves]
  cases run : evaluate first source with
  | mk result middle =>
    cases result with
    | none =>
      have secondBound := selection_path_work_bound second middle supported.2
      dsimp only
      omega
    | some value => dsimp only; omega
termination_by sizeOf p

/-- Actual selected-path budget for a fully preprocessed assignment. -/
theorem assignment_selected_path_bound {C F : Type}
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64)
    (target temp : Nat) (expression : WordLangExpHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F) :
    wordPathWork (Flapjack.Compiler.Backend.WordInst.instSelect config temp
      (.assign target expression)) source ≤ 4 * wordExpressionWork expression := by
  have grammar := raw_selection_straight_line config target temp
    (Flapjack.Compiler.Backend.WordInst.flattenExp
      (Flapjack.Compiler.Backend.WordInst.pullExp expression))
  have pathBound := selection_path_work_bound
    (Flapjack.Compiler.Backend.WordInst.instSelect config temp (.assign target expression))
    source (by simpa only [Flapjack.Compiler.Backend.WordInst.instSelect] using grammar)
  have leavesBound := assignment_selection_work_bound config target temp expression
  omega

#print axioms assignment_selected_path_bound
#print axioms selection_path_work_bound
end InitECandidate.Runtime.FineCost
