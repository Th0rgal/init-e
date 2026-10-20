import InitECandidate.Runtime.StackRemoveExecutedSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.If
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem removalCostSimulation_ite {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64) (yes no : HolProg 64)
    (localBound : 5 + gap ≤ sourcePrice (.ite cmp reg operand yes no))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (yesIH : RemovalCostSimulation sourcePrice gap jump yes source)
    (noIH : RemovalCostSimulation sourcePrice gap jump no source) :
    RemovalCostSimulation sourcePrice gap jump (.ite cmp reg operand yes no) source := by
  intro post target result pointer bounds premises
  obtain ⟨run, nonerror, related, lower⟩ := premises
  simp only [StackProps.regBound] at lower
  have leftEq := StackRemove.RelationLaws.stateRelGetVar jump bounds pointer reg source target ⟨related, lower.1⟩
  have rightEq := StackRemove.CompCorrect.If.operandLookup jump bounds pointer source target operand related lower.2.1
  rw [StackSemEvaluate.evaluate_ite] at run
  cases readLeft : StackSemStateOps.getVar reg source with
  | none =>
    rw [readLeft] at run
    exact False.elim (nonerror (Prod.mk.inj run).1.symm)
  | some left =>
    rw [readLeft] at run
    cases readRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source with
    | none =>
      rw [readRight] at run
      exact False.elim (nonerror (Prod.mk.inj run).1.symm)
    | some right =>
      rw [readRight] at run
      dsimp only at run
      cases chosen : wordSemWordCmp cmp left right with
      | none =>
        rw [chosen] at run
        exact False.elim (nonerror (Prod.mk.inj run).1.symm)
      | some choice =>
        rw [chosen] at run
        have branchRun : StackSemEvaluate.evaluate ((if choice then yes else no), source) = (result, post) := by
          cases choice <;> exact run
        have branchLower : StackProps.regBound (if choice then yes else no) pointer := by
          cases choice
          · exact lower.2.2.2
          · exact lower.2.2.1
        have branchIH : RemovalCostSimulation sourcePrice gap jump (if choice then yes else no) source := by
          cases choice <;> assumption
        obtain ⟨clock, postTarget, targetRun, postRelation, cost⟩ :=
          branchIH post target result pointer bounds ⟨branchRun, nonerror, related, branchLower⟩
        have targetLeft : StackSemStateOps.getVar reg {target with clock := clock + target.clock} = some left :=
          leftEq.symm.trans readLeft
        have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
            {target with clock := clock + target.clock} = some right := by
          have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} =
              StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
            cases operand <;> rfl
          exact same.trans (rightEq.symm.trans readRight)
        refine ⟨clock, postTarget, ?_, postRelation, ?_⟩
        · rw [StackRemove.comp, StackSemEvaluate.evaluate_ite, targetLeft, targetRight]
          cases choice <;> simpa only [chosen, Bool.false_eq_true, ↓reduceIte] using targetRun
        · rw [StackRemove.comp,
            stackExecutionCost.eq_2 (fun p _ => nativePriceWithGap gap p)
              {target with clock := clock + target.clock} cmp reg operand
              (StackRemove.comp jump bounds pointer yes) (StackRemove.comp jump bounds pointer no),
            stackExecutionCost.eq_2 (fun p _ => sourcePrice p) source cmp reg operand yes no]
          simp only [selectedBranchBudget, targetLeft, targetRight, readLeft, readRight, chosen]
          have targetLocal : nativePriceWithGap gap (.ite cmp reg operand
              (StackRemove.comp jump bounds pointer yes) (StackRemove.comp jump bounds pointer no)) = 5 + gap := rfl
          rw [targetLocal]
          cases choice <;> exact Nat.add_le_add localBound cost

#print axioms removalCostSimulation_ite
end InitECandidate.Runtime.StackToLab
