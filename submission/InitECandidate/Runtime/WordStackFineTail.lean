import InitECandidate.Runtime.WordStackExecutedTail
import InitECandidate.Runtime.WordExecutionCostLowerBound
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- A tail-call price absorbs its fixed lowering overhead once; the actual
reached callee retains the same coefficient. -/
theorem executedSimulation_tailCall {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (localBound : 41 ≤ factor * price (.call none dest args handler) source)
    (ih : ∀ (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat),
      WordSemStateFiniteExact.getVars args source = some xs ∧
      ¬ wordSemBadDestArgs dest args = true ∧
      wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat)) xs)
        source.code source.stackSize = some (args1, prog, ss) ∧
      handler = none ∧ source.clock ≠ 0 →
      ExecutedSimulation ac prog
        (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source))
        (factor * wordExecutionCost price prog
          (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source)))) :
    ExecutedSimulation ac (.call none dest args handler) source
      (factor * wordExecutionCost price (.call none dest args handler) source) := by
  let p : WordLangProgHOL (BitVec 64) := .call none dest args handler
  have simulation := ExecutedTail.executedSimulation_tailCall
    (factor * (wordExecutionCost price p source - price p source))
    ac dest args handler source covered (by
      intro xs args1 prog ss guards
      rcases guards with ⟨get, bad, find, noHandler, clock⟩
      have selected : wordExecutionCost price p source = price p source +
          wordExecutionCost price prog
            (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source)) := by
        dsimp only [p]
        rw [wordExecutionCost]
        simp only [get, bad, Bool.false_eq_true, ↓reduceIte, find, noHandler, clock, dite_false]
      rw [selected, Nat.add_sub_cancel_left]
      exact ih xs args1 prog ss ⟨get,bad,find,noHandler,clock⟩)
  apply simulation.mono
  have localLe := wordExecutionCost_local_le price p source
  have accounting : factor * (wordExecutionCost price p source - price p source) +
      factor * price p source = factor * wordExecutionCost price p source := by
    rw [← Nat.mul_add, Nat.sub_add_cancel localLe]
  change 41 ≤ factor * price p source at localBound
  change factor * (wordExecutionCost price p source - price p source) + 41 ≤
    factor * wordExecutionCost price p source
  omega

#print axioms executedSimulation_tailCall
end InitECandidate.Runtime.WordToStack
