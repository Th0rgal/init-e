import InitECandidate.Runtime.WordPullWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- Only the nonrecursive output forms emitted by raw expression selection. -/
def selectionStraightLine : WordLangProgHOL (BitVec 64) → Bool
  | .skip | .inst _ | .get _ _ | .opCurrHeap _ _ _ => true
  | .move _ moves => decide (moves.length = 1)
  | .seq first second => selectionStraightLine first && selectionStraightLine second
  | _ => false
termination_by p => sizeOf p

theorem raw_selection_straight_line (config : AsmConfigExact 64) (target temp : Nat)
    (expression : WordLangExpHOL (BitVec 64)) :
    selectionStraightLine (instSelectExp config target temp expression) = true := by
  cases expression with
  | const value | var value | lookup value => simp [instSelectExp, selectionStraightLine]
  | load address =>
    have addressBound := raw_selection_straight_line config temp temp address
    rw [instSelectExp.eq_def]
    dsimp only
    split
    · rename_i child offset
      split
      · have childBound := raw_selection_straight_line config temp temp child
        simp_all [selectionStraightLine]
        all_goals omega
      · have childBound := raw_selection_straight_line config temp temp
          (.op .add [child, .const offset])
        simp_all [selectionStraightLine]
        all_goals omega
    · simp_all [selectionStraightLine]
      all_goals omega
  | op operator args =>
    cases args with
    | nil => simp [instSelectExp, selectionStraightLine]
    | cons first tail =>
      cases tail with
      | nil => simp [instSelectExp, selectionStraightLine]
      | cons second tail =>
        cases tail with
        | cons third rest => simp [instSelectExp, selectionStraightLine]
        | nil =>
          rw [instSelectExp]
          split
          · have firstBound := raw_selection_straight_line config temp temp first
            simp_all [selectionStraightLine]
            all_goals omega
          · split
            · have secondBound := raw_selection_straight_line config temp temp second
              simp_all [selectionStraightLine]
              all_goals omega
            · have firstBound := raw_selection_straight_line config temp temp first
              have secondBound := raw_selection_straight_line config (temp+1) (temp+1) second
              split
              · rename_i value
                split
                · simp_all [selectionStraightLine]; try omega
                · split <;> simp_all [selectionStraightLine] <;> try omega
              · simp_all [selectionStraightLine]
                all_goals omega
  | shift operator operand amount =>
    have operandBound := raw_selection_straight_line config temp temp operand
    have amountBound := raw_selection_straight_line config (temp+1) (temp+1) amount
    rw [instSelectExp.eq_def]
    dsimp only
    split
    · rename_i value
      split
      · split <;> simp_all [selectionStraightLine] <;> try omega
      · simp_all [selectionStraightLine]; try omega
    · simp_all [selectionStraightLine]
      all_goals omega
termination_by sizeOf expression
  decreasing_by all_goals (subst_vars; simp_wf; try omega)


#print axioms raw_selection_straight_line
end InitECandidate.Runtime.FineCost
