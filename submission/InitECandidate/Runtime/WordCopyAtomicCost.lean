import InitECandidate.Runtime.WordCopyLocalCost
import InitECandidate.Runtime.WordCseAtomicCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Runtime.WordToStack

theorem copyPropInst_atomic (instruction : WordLangInst (BitVec 64))
    (aliases : WordCopy.CopyState) :
    wordCostAtomic (WordCopy.copyPropInst instruction aliases).1 = true := by
  cases instruction with
  | arith operation => cases operation <;> simp [WordCopy.copyPropInst, wordCostAtomic]
  | mem operation destination address =>
    cases address
    cases operation <;> simp [WordCopy.copyPropInst, wordCostAtomic]
  | _ => simp [WordCopy.copyPropInst, wordCostAtomic]

/-- Complete executed atomic copy-propagation cost, including shortened Gets
and renamed parallel assignments. No knowledge-validity assumption is needed
for cost alone; semantic correctness supplies that assumption separately. -/
theorem copyProp_atomic_executed_cost_le {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (aliases : WordCopy.CopyState)
    (source : WordSemStateFiniteExact 64 C F) (atomic : wordCostAtomic program = true) :
    wordExecutionCost wordOptimizerLocalPrice (WordCopy.copyPropProg program aliases).1 source ≤
      wordExecutionCost wordOptimizerLocalPrice program source := by
  cases program <;> simp only [wordCostAtomic, Bool.false_eq_true] at atomic
  case inst instruction =>
    simp only [WordCopy.copyPropProg]
    rw [wordExecutionCost_atomic _ _ _ (copyPropInst_atomic instruction aliases),
      wordExecutionCost_atomic _ _ _ rfl]
    exact copyPropInst_price_le instruction aliases source source
  case move priority pairs =>
    dsimp only [WordCopy.copyPropProg]
    split
    · simp only [wordExecutionCost, wordOptimizerLocalPrice]
      rw [copyPropMove_pairs_length]
    · exact Nat.le_refl _
  case get destination store =>
    dsimp only [WordCopy.copyPropProg]
    split
    · exact Nat.le_refl _
    · split
      · simp only [wordExecutionCost, wordOptimizerLocalPrice, copyPropMove_pairs_length]
        simp [refinedWordLocalPrice, refinedWordStackLeafBudget]
      · simp [wordExecutionCost, wordOptimizerLocalPrice,
          refinedWordLocalPrice, refinedWordStackLeafBudget]
  case set store expression =>
    cases expression <;> simp [WordCopy.copyPropProg, wordExecutionCost,
      wordOptimizerLocalPrice, refinedWordLocalPrice, refinedWordStackLeafBudget]
  all_goals simp [WordCopy.copyPropProg, wordExecutionCost,
    wordOptimizerLocalPrice, refinedWordLocalPrice, refinedWordStackLeafBudget]

#print axioms copyProp_atomic_executed_cost_le
end InitECandidate.Runtime.FineCost
