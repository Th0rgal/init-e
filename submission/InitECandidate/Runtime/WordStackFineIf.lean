import InitECandidate.Runtime.WordStackExecutedIf
import InitECandidate.Runtime.WordExecutionCostProps
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

private theorem wordCost_ite_selected {F : Type}
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (comparison : Cmp) (register : Nat) (operand : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (x y : WordLocW 64) (value : Bool)
    (left : WordSemStateFiniteExact.getVar register source = some x)
    (right : WordSemStateFiniteExact.getVarImm operand source = some y)
    (compared : wordSemWordCmp comparison x y = some value) :
    wordExecutionCost price (.ite comparison register operand first second) source =
      price (.ite comparison register operand first second) source +
        wordExecutionCost price (if value then first else second) source := by
  rw [wordExecutionCost]
  simp only [left, right, compared]
  cases value <;> rfl

/-- Conditional transfer charges only the branch selected by the actual
source comparison. Its coefficient does not grow with nesting depth. -/
theorem executedSimulation_ite {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec 64)) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (localBound : 30 ≤ factor * price (.ite comparison register operand first second) source)
    (firstIH : ∀ x y,
      WordSemStateFiniteExact.getVar register source = some x →
      WordSemStateFiniteExact.getVarImm operand source = some y →
      wordSemWordCmp comparison x y = some true →
      ExecutedSimulation ac first source (factor * wordExecutionCost price first source))
    (secondIH : ∀ x y,
      WordSemStateFiniteExact.getVar register source = some x →
      WordSemStateFiniteExact.getVarImm operand source = some y →
      wordSemWordCmp comparison x y = some false →
      ExecutedSimulation ac second source (factor * wordExecutionCost price second source)) :
    ExecutedSimulation ac (.ite comparison register operand first second) source
      (factor * wordExecutionCost price (.ite comparison register operand first second) source) := by
  let p : WordLangProgHOL (BitVec 64) := .ite comparison register operand first second
  have ih : ExecutedIf.OriginalInductionHypotheses
      (factor * (wordExecutionCost price p source - price p source))
      ac comparison register operand first second source := by
    constructor
    · intro v3 v4 x y value guards
      rcases guards with ⟨pair, rfl, rfl, compared, rfl⟩
      have reads := Prod.mk.inj pair
      have cost := wordCost_ite_selected price comparison register operand first second source
        x y true reads.1 reads.2 compared
      change ExecutedSimulation ac first source
        (factor * (wordExecutionCost price (.ite comparison register operand first second) source -
          price (.ite comparison register operand first second) source))
      rw [cost, Nat.add_sub_cancel_left]
      exact firstIH x y reads.1 reads.2 compared
    · intro v3 v4 x y value guards
      rcases guards with ⟨pair, rfl, rfl, compared, selected⟩
      have valueFalse : value = false := by cases value <;> simp_all
      subst value
      have reads := Prod.mk.inj pair
      have cost := wordCost_ite_selected price comparison register operand first second source
        x y false reads.1 reads.2 compared
      change ExecutedSimulation ac second source
        (factor * (wordExecutionCost price (.ite comparison register operand first second) source -
          price (.ite comparison register operand first second) source))
      rw [cost, Nat.add_sub_cancel_left]
      exact secondIH x y reads.1 reads.2 compared
  have simulation := ExecutedIf.compCorrectIf
    (factor * (wordExecutionCost price p source - price p source))
    ac comparison register operand first second source ih
  apply simulation.mono
  have localLe : price p source ≤ wordExecutionCost price p source := by
    rw [wordExecutionCost]
    exact Nat.le_add_right _ _
  have accounting : factor * (wordExecutionCost price p source - price p source) +
      factor * price p source = factor * wordExecutionCost price p source := by
    rw [← Nat.mul_add, Nat.sub_add_cancel localLe]
  change factor * (wordExecutionCost price p source - price p source) + 30 ≤
    factor * wordExecutionCost price p source
  change 30 ≤ factor * price p source at localBound
  omega

#print axioms executedSimulation_ite
end InitECandidate.Runtime.WordToStack
