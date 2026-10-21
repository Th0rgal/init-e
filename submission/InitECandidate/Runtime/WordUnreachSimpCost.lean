import InitECandidate.Runtime.WordUnreachMoveCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

theorem optimizer_seq_skip_right_cost_eq {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (.seq program .skip) source =
      wordExecutionCost wordOptimizerLocalPrice program source := by
  rw [wordExecutionCost_seq]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  rcases actual : evaluate program source with ⟨result, middle⟩
  cases result <;> simp [wordExecutionCost, wordOptimizerLocalPrice,
    WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]

theorem optimizer_seq_skip_left_cost_eq {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (.seq .skip program) source =
      wordExecutionCost wordOptimizerLocalPrice program source := by
  rw [wordExecutionCost_seq]
  rw [evaluate, wordExecutionCost]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  all_goals simp

theorem optimizer_seq_stopped_cost_eq {C F : Type}
    (first second : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (stops : (evaluate first source).1.isSome = true) :
    wordExecutionCost wordOptimizerLocalPrice (.seq first second) source =
      wordExecutionCost wordOptimizerLocalPrice first source := by
  rw [wordExecutionCost_seq]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  rcases actual : evaluate first source with ⟨result, middle⟩
  cases result with
  | none => simp only [actual, Option.isSome_none, Bool.false_eq_true] at stops
  | some outcome => exact Nat.add_zero _

def wordImmediateTransfer {α : Type} : WordLangProgHOL α → Bool
  | .raise _ | .return _ _ | .break _ | .continue _ => true
  | _ => false

theorem optimizer_immediate_transfer_stops {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (transfer : wordImmediateTransfer program = true) :
    (evaluate program source).1.isSome = true := by
  cases program <;> simp only [wordImmediateTransfer, Bool.false_eq_true] at transfer
  all_goals rw [evaluate]
  all_goals repeat' split
  all_goals rfl

theorem optimizer_destSeqMove_shape (program : WordLangProgHOL (BitVec 64))
    (priority : Nat) (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec 64))
    (found : WordUnreach.destSeqMove program = some (priority, moves, rest)) :
    (program = .move priority moves ∧ rest = .skip) ∨
      program = .seq (.move priority moves) rest := by
  cases program with
  | move p pairs =>
    simp only [WordUnreach.destSeqMove, Option.some.injEq, Prod.mk.injEq] at found
    rcases found with ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩
  | seq first second =>
    cases first <;> simp only [WordUnreach.destSeqMove, Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at found
    rcases found with ⟨rfl, rfl, rfl⟩
    exact Or.inr rfl
  | _ => simp only [WordUnreach.destSeqMove, reduceCtorEq] at found

/-- Every `SimpSeq` optimization is quantitatively justified at the actual
execution counter: Skip removal, terminal suffix deletion and move merging. -/
theorem optimizer_simpSeq_cost_le {C F : Type}
    (first second : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.seq first second) source).1 ≠ some .error) :
    wordExecutionCost wordOptimizerLocalPrice (WordUnreach.simpSeq first second) source ≤
      wordExecutionCost wordOptimizerLocalPrice (.seq first second) source := by
  unfold WordUnreach.simpSeq
  by_cases secondSkip : second = .skip
  · rw [if_pos secondSkip, secondSkip, optimizer_seq_skip_right_cost_eq]
  rw [if_neg secondSkip]
  cases first
  case skip => rw [optimizer_seq_skip_left_cost_eq]
  case raise register =>
    rw [optimizer_seq_stopped_cost_eq _ _ _ (optimizer_immediate_transfer_stops _ _ rfl)]
  case «return» location values =>
    rw [optimizer_seq_stopped_cost_eq _ _ _ (optimizer_immediate_transfer_stops _ _ rfl)]
  case «break» label =>
    rw [optimizer_seq_stopped_cost_eq _ _ _ (optimizer_immediate_transfer_stops _ _ rfl)]
  case «continue» label =>
    rw [optimizer_seq_stopped_cost_eq _ _ _ (optimizer_immediate_transfer_stops _ _ rfl)]
  case move priority pairs =>
    dsimp only
    cases found : WordUnreach.destSeqMove second with
    | none => exact Nat.le_refl _
    | some data =>
      rcases data with ⟨otherPriority, otherPairs, rest⟩
      dsimp only
      rcases optimizer_destSeqMove_shape second otherPriority otherPairs rest found with
        ⟨rfl, rfl⟩ | rfl
      · simp only [if_true]
        exact optimizer_merged_move_cost_le _ _ _ _ _ source
          (optimizer_move_nonerror_normal _ _ source (optimizer_seq_prefix_safe _ _ source safe))
      · have prefixSafe :
          (evaluate (.seq (.move priority pairs) (.move otherPriority otherPairs)) source).1 ≠
            some .error := by
          have reassociated :
              (evaluate (.seq (.seq (.move priority pairs) (.move otherPriority otherPairs)) rest) source).1 ≠
                some .error := by rwa [← WordUnreach.evaluateSeqAssoc]
          exact optimizer_seq_prefix_safe _ _ source reassociated
        by_cases restSkip : rest = .skip
        · rw [if_pos restSkip]
          subst restSkip
          rw [← optimizer_seq_assoc_cost_eq, optimizer_seq_skip_right_cost_eq]
          exact optimizer_merged_move_cost_le _ _ _ _ _ source
            (optimizer_move_nonerror_normal _ _ source (optimizer_seq_prefix_safe _ _ source prefixSafe))
        · rw [if_neg restSkip]
          exact optimizer_merge_moves_suffix_cost_le _ _ _ _ _ rest source prefixSafe
  all_goals exact Nat.le_refl _

#print axioms optimizer_simpSeq_cost_le
#print axioms optimizer_seq_stopped_cost_eq
end InitECandidate.Runtime.FineCost
