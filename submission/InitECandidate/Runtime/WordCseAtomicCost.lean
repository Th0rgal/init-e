import InitECandidate.Runtime.WordCseLocalCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Runtime.WordToStack

/-- Nodes whose executed cost has no recursive program contribution. -/
def wordCostAtomic {α : Type} : WordLangProgHOL α → Bool
  | .seq _ _ | .ite _ _ _ _ _ | .loop _ _ _ | .mustTerminate _ | .call _ _ _ _ => false
  | _ => true

theorem wordExecutionCost_atomic {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (atomic : wordCostAtomic program = true) :
    wordExecutionCost price program source = price program source := by
  cases program <;> simp_all only [wordCostAtomic, Bool.false_eq_true, wordExecutionCost]

theorem cse_addToDataAux_atomic (data : WordCse.Knowledge) (destination : Nat)
    (key : List Nat) (original : WordLangProgHOL (BitVec 64))
    (atomic : wordCostAtomic original = true) :
    wordCostAtomic (WordCse.addToDataAux data destination key original).2 = true := by
  unfold WordCse.addToDataAux
  split <;> split <;> simp_all only [wordCostAtomic]

theorem cse_addToLoadAux_atomic (data : WordCse.Knowledge) (destination : Nat)
    (key : List Nat) (original : WordLangProgHOL (BitVec 64))
    (atomic : wordCostAtomic original = true) :
    wordCostAtomic (WordCse.addToLoadAux data destination key original).2 = true := by
  unfold WordCse.addToLoadAux
  split <;> split <;> simp_all only [wordCostAtomic]

theorem cse_instruction_atomic (data : WordCse.Knowledge)
    (instruction : Compiler.Encoders.Asm.HolInst 64) :
    wordCostAtomic (WordCse.wordCseInst data instruction).2 = true := by
  cases instruction with
  | skip => rfl
  | const destination value =>
    dsimp only [WordCse.wordCseInst]
    split
    · rfl
    · dsimp only [WordCse.addToDataConst]
      split <;> rfl
  | arith operation =>
    dsimp only [WordCse.wordCseInst]
    split
    · unfold WordCse.addToData
      exact cse_addToDataAux_atomic _ _ _ _ rfl
    · rfl
  | mem operation destination address =>
    cases address
    dsimp only [WordCse.wordCseInst]
    split
    · rfl
    · split
      · rfl
      · exact cse_addToLoadAux_atomic _ _ _ _ rfl

theorem cse_instruction_executed_cost_le {C F : Type}
    (data : WordCse.Knowledge) (instruction : WordLangInst (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice
      (WordCse.wordCse data (.inst instruction)).2 source ≤
    wordExecutionCost wordOptimizerLocalPrice (.inst instruction) source := by
  simp only [WordCse.wordCse]
  rw [wordExecutionCost_atomic _ _ _
    (cse_instruction_atomic data (Compiler.Encoders.Asm.HolInst.ofWordLangInst instruction)),
    wordExecutionCost_atomic _ _ _ rfl]
  simpa only [WordCse.wordCse, Compiler.Encoders.Asm.HolInst.to_of] using
    cse_instruction_price_le data (Compiler.Encoders.Asm.HolInst.ofWordLangInst instruction) source source

#print axioms cse_instruction_executed_cost_le

/-- All atomic CSE cases are bounded in the actual execution counter. This
includes CSE hits, not merely instructions that were left syntactically equal. -/
theorem cse_atomic_executed_cost_le {C F : Type}
    (data : WordCse.Knowledge) (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F) (atomic : wordCostAtomic program = true) :
    wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse data program).2 source ≤
      wordExecutionCost wordOptimizerLocalPrice program source := by
  cases program <;> simp only [wordCostAtomic, Bool.false_eq_true] at atomic
  case inst instruction => exact cse_instruction_executed_cost_le data instruction source
  case get destination store =>
    cases found : (WordCse.invalidateData data destination).getsMem.lookup store <;>
      by_cases even : destination % 2 = 0 <;>
      simp [WordCse.wordCse, WordCse.getClause, found, even, wordExecutionCost,
        wordOptimizerLocalPrice, refinedWordLocalPrice, refinedWordStackLeafBudget]
  case opCurrHeap operation destination register =>
    dsimp only [WordCse.wordCse]
    split
    · exact Nat.le_refl _
    · unfold WordCse.addToDataAux
      split <;> split <;>
        simp [wordExecutionCost, wordOptimizerLocalPrice, refinedWordLocalPrice,
          refinedWordStackLeafBudget]
  case locValue destination location =>
    dsimp only [WordCse.wordCse]
    unfold WordCse.addToDataAux
    split <;> split <;>
      simp [wordExecutionCost, wordOptimizerLocalPrice, refinedWordLocalPrice,
        refinedWordStackLeafBudget]
  case set store expression =>
    dsimp only [WordCse.wordCse, WordCse.setClause]
    split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · split <;> exact Nat.le_refl _
  all_goals exact Nat.le_refl _

#print axioms cse_atomic_executed_cost_le
#print axioms wordExecutionCost_atomic
end InitECandidate.Runtime.FineCost
