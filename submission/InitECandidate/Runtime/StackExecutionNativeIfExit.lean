import InitECandidate.Runtime.StackExecutionNativeIf
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- Actual exit true arm, covering all conditional layouts and no unselected body work. -/
theorem exitExecutionCost_if_true {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (result : StackSemResult 64)
    (chosen : wordSemWordCmp cmp x y = some true)
    (exits : (StackSemEvaluate.evaluate (yes, source)).1 = some result)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (bodyBound : ExitWeightedFlatten yes source result (executionCostPrice price yes source)) :
    ExitWeightedFlatten (.ite cmp reg operand yes no) source result
      (executionCostPrice price (.ite cmp reg operand yes no) source) := by
  classical
  have budget := executionCost_if_budget price yes no cmp reg operand source x y true lhs rhs chosen localPrice
  have selectedNe : yes ≠ .skip := by
    intro eq
    rw [eq, StackSemEvaluate.evaluate_skip] at exits
    contradiction
  have selectedNonSkip := executionNonSkip_of_ne yes selectedNe
  by_cases otherSkip : no = .skip
  · subst no
    apply (exitWeightedFlatten_skipIf_true yes selectedNonSkip cmp reg operand source x y lhs rhs chosen
      (executionCostPrice price yes source) result bodyBound).mono
    intro encoded pc
    have h := budget encoded pc
    simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
    omega
  · have otherNonSkip := executionNonSkip_of_ne no otherSkip
    cases yesFlag : (stackFlattenShape yes).1
    · cases noFlag : (stackFlattenShape no).1
      · apply (exitWeightedFlatten_generalIf_true yes no selectedNonSkip otherNonSkip yesFlag noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price yes source) result bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        simp only [LabToTarget.controlWork] at h ⊢
        omega
      · apply (exitWeightedFlatten_noNoRetIf_true yes no selectedNonSkip otherNonSkip yesFlag noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price yes source) result bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        simp only [LabToTarget.controlWork] at h ⊢
        omega
    · apply (exitWeightedFlatten_yesNoRetIf_true yes no selectedNonSkip otherNonSkip yesFlag
        cmp reg operand source x y lhs rhs chosen (executionCostPrice price yes source) result bodyBound).mono
      intro encoded pc
      have h := budget encoded pc
      simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
      simp only [LabToTarget.controlWork] at h ⊢
      omega

/-- Actual exit false arm, covering all conditional layouts and no unselected body work. -/
theorem exitExecutionCost_if_false {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (result : StackSemResult 64)
    (chosen : wordSemWordCmp cmp x y = some false)
    (exits : (StackSemEvaluate.evaluate (no, source)).1 = some result)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (bodyBound : ExitWeightedFlatten no source result (executionCostPrice price no source)) :
    ExitWeightedFlatten (.ite cmp reg operand yes no) source result
      (executionCostPrice price (.ite cmp reg operand yes no) source) := by
  classical
  have budget := executionCost_if_budget price yes no cmp reg operand source x y false lhs rhs chosen localPrice
  have selectedNe : no ≠ .skip := by
    intro eq
    rw [eq, StackSemEvaluate.evaluate_skip] at exits
    contradiction
  have selectedNonSkip := executionNonSkip_of_ne no selectedNe
  by_cases otherSkip : yes = .skip
  · subst yes
    apply (exitWeightedFlatten_thenSkipIf_false no selectedNonSkip cmp reg operand source x y lhs rhs chosen
      (executionCostPrice price no source) result bodyBound).mono
    intro encoded pc
    have h := budget encoded pc
    simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
    omega
  · have otherNonSkip := executionNonSkip_of_ne yes otherSkip
    cases yesFlag : (stackFlattenShape yes).1
    · cases noFlag : (stackFlattenShape no).1
      · apply (exitWeightedFlatten_generalIf_false yes no otherNonSkip selectedNonSkip yesFlag noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price no source) result bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        simp only [LabToTarget.controlWork] at h ⊢
        omega
      · apply (exitWeightedFlatten_noNoRetIf_false yes no otherNonSkip selectedNonSkip yesFlag noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price no source) result bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        simp only [LabToTarget.controlWork] at h ⊢
        omega
    · apply (exitWeightedFlatten_yesNoRetIf_false yes no otherNonSkip selectedNonSkip yesFlag
        cmp reg operand source x y lhs rhs chosen (executionCostPrice price no source) result bodyBound).mono
      intro encoded pc
      have h := budget encoded pc
      simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
      simp only [LabToTarget.controlWork] at h ⊢
      omega

/-- Actual terminal true arm, covering all conditional layouts and no unselected body work. -/
theorem terminalExecutionCost_if_true {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (chosen : wordSemWordCmp cmp x y = some true)
    (exits : (StackSemEvaluate.evaluate (yes, source)).1 = some result)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (bodyBound : TerminalWeightedFlatten yes source result outcome (executionCostPrice price yes source)) :
    TerminalWeightedFlatten (.ite cmp reg operand yes no) source result outcome
      (executionCostPrice price (.ite cmp reg operand yes no) source) := by
  classical
  have budget := executionCost_if_budget price yes no cmp reg operand source x y true lhs rhs chosen localPrice
  have selectedNe : yes ≠ .skip := by
    intro eq
    rw [eq, StackSemEvaluate.evaluate_skip] at exits
    contradiction
  have selectedNonSkip := executionNonSkip_of_ne yes selectedNe
  by_cases otherSkip : no = .skip
  · subst no
    apply (terminalWeightedFlatten_skipIf_true yes selectedNonSkip cmp reg operand source x y lhs rhs chosen
      (executionCostPrice price yes source) result outcome bodyBound).mono
    intro encoded pc
    have h := budget encoded pc
    simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
    omega
  · have otherNonSkip := executionNonSkip_of_ne no otherSkip
    cases yesFlag : (stackFlattenShape yes).1
    · cases noFlag : (stackFlattenShape no).1
      · apply (terminalWeightedFlatten_generalIf_true yes no selectedNonSkip otherNonSkip yesFlag noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price yes source) result outcome bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        simp only [LabToTarget.controlWork] at h ⊢
        omega
      · apply (terminalWeightedFlatten_noNoRetIf_true yes no selectedNonSkip otherNonSkip yesFlag noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price yes source) result outcome bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        simp only [LabToTarget.controlWork] at h ⊢
        omega
    · apply (terminalWeightedFlatten_yesNoRetIf_true yes no selectedNonSkip otherNonSkip yesFlag
        cmp reg operand source x y lhs rhs chosen (executionCostPrice price yes source) result outcome bodyBound).mono
      intro encoded pc
      have h := budget encoded pc
      simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
      simp only [LabToTarget.controlWork] at h ⊢
      omega

/-- Actual terminal false arm, covering all conditional layouts and no unselected body work. -/
theorem terminalExecutionCost_if_false {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (chosen : wordSemWordCmp cmp x y = some false)
    (exits : (StackSemEvaluate.evaluate (no, source)).1 = some result)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (bodyBound : TerminalWeightedFlatten no source result outcome (executionCostPrice price no source)) :
    TerminalWeightedFlatten (.ite cmp reg operand yes no) source result outcome
      (executionCostPrice price (.ite cmp reg operand yes no) source) := by
  classical
  have budget := executionCost_if_budget price yes no cmp reg operand source x y false lhs rhs chosen localPrice
  have selectedNe : no ≠ .skip := by
    intro eq
    rw [eq, StackSemEvaluate.evaluate_skip] at exits
    contradiction
  have selectedNonSkip := executionNonSkip_of_ne no selectedNe
  by_cases otherSkip : yes = .skip
  · subst yes
    apply (terminalWeightedFlatten_thenSkipIf_false no selectedNonSkip cmp reg operand source x y lhs rhs chosen
      (executionCostPrice price no source) result outcome bodyBound).mono
    intro encoded pc
    have h := budget encoded pc
    simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
    omega
  · have otherNonSkip := executionNonSkip_of_ne yes otherSkip
    cases yesFlag : (stackFlattenShape yes).1
    · cases noFlag : (stackFlattenShape no).1
      · apply (terminalWeightedFlatten_generalIf_false yes no otherNonSkip selectedNonSkip yesFlag noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price no source) result outcome bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        simp only [LabToTarget.controlWork] at h ⊢
        omega
      · apply (terminalWeightedFlatten_noNoRetIf_false yes no otherNonSkip selectedNonSkip yesFlag noFlag
          cmp reg operand source x y lhs rhs chosen (executionCostPrice price no source) result outcome bodyBound).mono
        intro encoded pc
        have h := budget encoded pc
        simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
        simp only [LabToTarget.controlWork] at h ⊢
        omega
    · apply (terminalWeightedFlatten_yesNoRetIf_false yes no otherNonSkip selectedNonSkip yesFlag
        cmp reg operand source x y lhs rhs chosen (executionCostPrice price no source) result outcome bodyBound).mono
      intro encoded pc
      have h := budget encoded pc
      simp only [executionCostPrice, Bool.false_eq_true, ↓reduceIte] at h ⊢
      simp only [LabToTarget.controlWork] at h ⊢
      omega

#print axioms exitExecutionCost_if_true
#print axioms exitExecutionCost_if_false
#print axioms terminalExecutionCost_if_true
#print axioms terminalExecutionCost_if_false
end InitECandidate.Runtime.StackToLab
