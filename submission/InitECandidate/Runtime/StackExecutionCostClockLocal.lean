import InitECandidate.Runtime.StackExecutionCostClockJump
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem costClockStableAt_seq {F : Type} (price : HolProg 64 → Nat) (first second : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (firstStable : CostClockStableAt price first source)
    (secondStable : ∀ middle, StackSemEvaluate.evaluate (first, source) = (none, middle) →
      CostClockStableAt price second middle) :
    CostClockStableAt price (.seq first second) source := by
  intro post result run notTimeout extra
  have rootRun := run
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨firstResult, middle⟩
  rw [firstRun] at run
  have firstNotTimeout : firstResult ≠ some .timeOut := by
    intro eq
    rw [eq] at run
    exact notTimeout (Prod.mk.inj run).1.symm
  have shifted := StackProps.evaluateAddClock extra first source firstResult middle ⟨firstRun, firstNotTimeout⟩
  rw [stackExecutionCost_seq, stackExecutionCost_seq, firstRun, shifted,
    firstStable middle firstResult firstRun firstNotTimeout extra]
  cases firstResult with
  | none =>
    dsimp only
    rw [secondStable middle firstRun post result run notTimeout extra]
  | some value => rfl

theorem costClockStableAt_ite {F : Type} (price : HolProg 64 → Nat) (cmp : HolCmp)
    (reg : Nat) (operand : HolRegImm 64) (yes no : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (yesStable : CostClockStableAt price yes source)
    (noStable : CostClockStableAt price no source) :
    CostClockStableAt price (.ite cmp reg operand yes no) source := by
  intro post result run notTimeout extra
  rw [StackSemEvaluate.evaluate_ite] at run
  rw [stackExecutionCost, stackExecutionCost]
  unfold selectedBranchBudget
  have readVar : StackSemStateOps.getVar reg {source with clock := source.clock + extra} =
      StackSemStateOps.getVar reg source := by simp [StackSemStateOps.getVar]
  have readImm : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) {source with clock := source.clock + extra} =
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source := by
    cases operand <;> simp [HolRegImm.toWordRegImm, StackSemStateOps.getVarImm, StackSemStateOps.getVar]
  rw [readVar, readImm]
  split at run
  · rename_i x y lhs rhs
    simp only [lhs, rhs]
    split at run
    · rename_i choice
      rw [choice, yesStable post result run notTimeout extra]
    · rename_i choice
      rw [choice, noStable post result run notTimeout extra]
    · rename_i choice
      rw [choice]
  · rename_i failed
    split <;> simp_all

#print axioms costClockStableAt_seq
#print axioms costClockStableAt_ite
end InitECandidate.Runtime.StackToLab
