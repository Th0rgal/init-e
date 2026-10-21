import InitECandidate.Runtime.WordStackFineLeaf
import InitECandidate.Runtime.LoopWordPrice
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- The actual source-to-Word price table pays every proved primitive
lowering cost with coefficient 64; free structural primitives stay free. -/
theorem wordStackLeafBudget_loopWordPrice {F : Type}
    (p : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (budget : Nat) (priced : wordStackLeafBudget p = some budget) :
    budget ≤ 64 * loopWordPrice p source := by
  cases p <;> simp only [wordStackLeafBudget, Option.some.injEq, reduceCtorEq] at priced
  all_goals subst budget
  all_goals simp only [loopWordPrice]
  all_goals omega

/-- Primitive transfer for the concrete fine Word cost used by the
Pancake/Loop compiler proof, without an assumed local or target cost bound. -/
theorem executedSimulation_loopWord_leaf {F : Type} (ac : AsmConfigExact 64)
    (p : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (budget : Nat) (priced : wordStackLeafBudget p = some budget) :
    ExecutedSimulation ac p source (64 * wordExecutionCost loopWordPrice p source) :=
  executedSimulation_fine_leaf ac loopWordPrice 64 p source budget priced
    (wordStackLeafBudget_loopWordPrice p source budget priced)

#print axioms wordStackLeafBudget_loopWordPrice
#print axioms executedSimulation_loopWord_leaf
end InitECandidate.Runtime.WordToStack
