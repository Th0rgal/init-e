import InitECandidate.Runtime.StackExecutionCostProps
import InitECandidate.Runtime.StackExecutionEligibility
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Cost stability under adding unused fuel, for an actual completed execution. -/
def CostClockStable {F : Type} (price : HolProg 64 → Nat) (p : HolProg 64) : Prop :=
  ∀ (source post : StackSemStateFiniteExact 64 LabToTarget.Config F) result,
    StackSemEvaluate.evaluate (p, source) = (result, post) → result ≠ some .timeOut →
    ∀ extra, stackExecutionCost (fun p _ => price p) p {source with clock := source.clock + extra} =
      stackExecutionCost (fun p _ => price p) p source

theorem costClockStable_seq {F : Type} (price : HolProg 64 → Nat) (first second : HolProg 64)
    (firstStable : CostClockStable (F := F) price first)
    (secondStable : CostClockStable (F := F) price second) :
    CostClockStable (F := F) price (.seq first second) := by
  intro source post result run notTimeout extra
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
    firstStable source middle firstResult firstRun firstNotTimeout extra]
  cases firstResult with
  | none =>
    dsimp only
    rw [secondStable middle post result run notTimeout extra]
  | some value => rfl

theorem costClockStable_ite {F : Type} (price : HolProg 64 → Nat) (cmp : HolCmp)
    (reg : Nat) (operand : HolRegImm 64) (yes no : HolProg 64)
    (yesStable : CostClockStable (F := F) price yes)
    (noStable : CostClockStable (F := F) price no) :
    CostClockStable (F := F) price (.ite cmp reg operand yes no) := by
  intro source post result run notTimeout extra
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
      rw [choice, yesStable source post result run notTimeout extra]
    · rename_i choice
      rw [choice, noStable source post result run notTimeout extra]
    · rename_i choice
      rw [choice]
  · rename_i failed
    split <;> simp_all

theorem costClockStable_atomic {F : Type} (price : HolProg 64 → Nat) (p : HolProg 64)
    (atomic : executionAtomic p = true) : CostClockStable (F := F) price p := by
  cases p <;> simp only [executionAtomic, Bool.false_eq_true] at atomic
  all_goals intro source post result run notTimeout extra
  all_goals simp [stackExecutionCost]

#print axioms costClockStable_atomic
#print axioms costClockStable_seq
#print axioms costClockStable_ite
end InitECandidate.Runtime.StackToLab
