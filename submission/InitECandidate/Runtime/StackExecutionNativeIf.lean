import InitECandidate.Runtime.StackExecutionNativeBasis
import InitECandidate.Runtime.StackWeightedNoRetIf
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers

theorem executionNonSkip_of_ne (body : HolProg 64) (h : body ≠ .skip) :
    Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false := by
  cases body <;> simp_all [Flapjack.Compiler.Backend.StackToLab.stackIsSkip]

/-- A body that actually falls through cannot have a static no-return flag. -/
private theorem shape_normal_of_run {F : Type} (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (normal : (StackSemEvaluate.evaluate (body, source)).1 = none) :
    (stackFlattenShape body).1 = false := by
  cases flag : (stackFlattenShape body).1
  · rfl
  · have h := noRetCorrect false body 0 0 [] [] (by rw [stackFlatten_noRet]; exact flag) source
    rw [normal] at h
    contradiction

theorem executionCost_if_budget {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64) (choice : Bool)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some choice)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (encoded : LabProgHOL 64) (pc : Nat) :
    LabToTarget.controlWork 3 encoded pc + 2 +
      executionCostPrice price (if choice then yes else no) source encoded 0 ≤
      executionCostPrice price (.ite cmp reg operand yes no) source encoded pc := by
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_2]
  have selected := selectedBranchBudget_eq cmp reg operand source
    (stackExecutionCost (fun p s => price p s encoded) yes source)
    (stackExecutionCost (fun p s => price p s encoded) no source) choice ⟨x, y, lhs, rhs, chosen⟩
  rw [selected]
  have h := localPrice encoded pc
  cases choice <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- Actual normal true arm, covering every compiler conditional layout. -/
theorem normalExecutionCost_if_true {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (normal : (StackSemEvaluate.evaluate (yes, source)).1 = none)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (bodyBound : NormalWeightedFlatten yes source (executionCostPrice price yes source)) :
    NormalWeightedFlatten (.ite cmp reg operand yes no) source
      (executionCostPrice price (.ite cmp reg operand yes no) source) := by
  classical
  have budget := executionCost_if_budget price yes no cmp reg operand source x y true lhs rhs chosen localPrice
  by_cases yesSkip : yes = .skip
  · subst yes
    by_cases noSkip : no = .skip
    · subst no
      apply (normalWeightedFlatten_bothSkipIf cmp reg operand source x y lhs rhs true chosen).mono
      intro encoded pc
      exact Nat.zero_le _
    · have noNonSkip := executionNonSkip_of_ne no noSkip
      apply (normalWeightedFlatten_thenSkipIf_true no noNonSkip cmp reg operand source x y lhs rhs chosen).mono
      intro encoded pc
      have h := budget encoded pc
      simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
      unfold LabToTarget.controlWork at h
      omega
  · have yesNonSkip := executionNonSkip_of_ne yes yesSkip
    by_cases noSkip : no = .skip
    · subst no
      apply (normalWeightedFlatten_skipIf_true yes yesNonSkip cmp reg operand source x y lhs rhs chosen
        (executionCostPrice price yes source) bodyBound).mono
      intro encoded pc
      have h := budget encoded pc
      simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
      omega
    · have noNonSkip := executionNonSkip_of_ne no noSkip
      have selectedNormal := shape_normal_of_run yes source normal
      cases noFlag : (stackFlattenShape no).1
      · apply (normalWeightedFlatten_generalIf_true yes no yesNonSkip noNonSkip selectedNormal noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price yes source) bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        unfold LabToTarget.controlWork at h
        omega
      · apply (normalWeightedFlatten_noNoRetIf_true yes no yesNonSkip noNonSkip selectedNormal noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price yes source) bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        unfold LabToTarget.controlWork at h
        omega

/-- Actual normal false arm, covering every compiler conditional layout. -/
theorem normalExecutionCost_if_false {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (normal : (StackSemEvaluate.evaluate (no, source)).1 = none)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (bodyBound : NormalWeightedFlatten no source (executionCostPrice price no source)) :
    NormalWeightedFlatten (.ite cmp reg operand yes no) source
      (executionCostPrice price (.ite cmp reg operand yes no) source) := by
  classical
  have budget := executionCost_if_budget price yes no cmp reg operand source x y false lhs rhs chosen localPrice
  by_cases yesSkip : yes = .skip
  · subst yes
    by_cases noSkip : no = .skip
    · subst no
      apply (normalWeightedFlatten_bothSkipIf cmp reg operand source x y lhs rhs false chosen).mono
      intro encoded pc
      exact Nat.zero_le _
    · have noNonSkip := executionNonSkip_of_ne no noSkip
      apply (normalWeightedFlatten_thenSkipIf_false no noNonSkip cmp reg operand source x y lhs rhs chosen
        (executionCostPrice price no source) bodyBound).mono
      intro encoded pc
      have h := budget encoded pc
      simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
      omega
  · have yesNonSkip := executionNonSkip_of_ne yes yesSkip
    by_cases noSkip : no = .skip
    · subst no
      apply (normalWeightedFlatten_skipIf_false yes yesNonSkip cmp reg operand source x y lhs rhs chosen).mono
      intro encoded pc
      have h := budget encoded pc
      simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
      unfold LabToTarget.controlWork at h
      omega
    · have noNonSkip := executionNonSkip_of_ne no noSkip
      have selectedNormal := shape_normal_of_run no source normal
      cases yesFlag : (stackFlattenShape yes).1
      · apply (normalWeightedFlatten_generalIf_false yes no yesNonSkip noNonSkip yesFlag selectedNormal
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price no source) bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        omega
      · apply (normalWeightedFlatten_yesNoRetIf_false yes no yesNonSkip noNonSkip yesFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price no source) bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        unfold LabToTarget.controlWork at h
        omega

#print axioms normalExecutionCost_if_true
#print axioms normalExecutionCost_if_false
end InitECandidate.Runtime.StackToLab
