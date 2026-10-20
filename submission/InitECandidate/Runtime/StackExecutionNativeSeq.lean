import InitECandidate.Runtime.StackExecutionNativeBasis
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- The executed cost of a normal prefix composes with its reached normal suffix. -/
theorem normalExecutionCost_seq_next {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (first second : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (firstRun : StackSemEvaluate.evaluate (first, source) = (none, middle))
    (firstBound : NormalWeightedFlatten first source (executionCostPrice price first source))
    (secondBound : NormalWeightedFlatten second middle (executionCostPrice price second middle)) :
    NormalWeightedFlatten (.seq first second) source (executionCostPrice price (.seq first second) source) := by
  refine normalWeightedFlatten_seq first second source
    (executionCostPrice price first source) (executionCostPrice price second middle)
    firstBound ?_ (executionCostPrice price (.seq first second) source) ?_
  · intro actual run
    have eq : actual = middle := (Prod.mk.inj (run.symm.trans firstRun)).2
    subst actual
    exact secondBound
  · intro encoded pc sectionId labelId continues breaks
    simp only [executionCostPrice, stackExecutionCost_seq, firstRun]
    omega

/-- The executed cost of a normal prefix composes with its reached exit suffix. -/
theorem exitExecutionCost_seq_next {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (first second : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64)
    (firstRun : StackSemEvaluate.evaluate (first, source) = (none, middle))
    (firstBound : NormalWeightedFlatten first source (executionCostPrice price first source))
    (secondBound : ExitWeightedFlatten second middle result (executionCostPrice price second middle)) :
    ExitWeightedFlatten (.seq first second) source result (executionCostPrice price (.seq first second) source) := by
  refine exitWeightedFlatten_seq_next first second source result
    (by rw [firstRun]) (executionCostPrice price first source) (executionCostPrice price second middle)
    firstBound ?_ (executionCostPrice price (.seq first second) source) ?_
  · intro actual run
    have eq : actual = middle := (Prod.mk.inj (run.symm.trans firstRun)).2
    subst actual
    exact secondBound
  · intro encoded pc sectionId labelId continues breaks
    simp only [executionCostPrice, stackExecutionCost_seq, firstRun]
    omega

/-- The executed cost of a normal prefix composes with its reached terminal suffix. -/
theorem terminalExecutionCost_seq_next {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (first second : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (firstRun : StackSemEvaluate.evaluate (first, source) = (none, middle))
    (firstBound : NormalWeightedFlatten first source (executionCostPrice price first source))
    (secondBound : TerminalWeightedFlatten second middle result outcome (executionCostPrice price second middle)) :
    TerminalWeightedFlatten (.seq first second) source result outcome (executionCostPrice price (.seq first second) source) := by
  refine terminalWeightedFlatten_seq_next first second source result outcome
    (by rw [firstRun]) (executionCostPrice price first source) (executionCostPrice price second middle)
    firstBound ?_ (executionCostPrice price (.seq first second) source) ?_
  · intro actual run
    have eq : actual = middle := (Prod.mk.inj (run.symm.trans firstRun)).2
    subst actual
    exact secondBound
  · intro encoded pc sectionId labelId continues breaks
    simp only [executionCostPrice, stackExecutionCost_seq, firstRun]
    omega

/-- An early exit exit leaves the second subtree uncharged by the executed model. -/
theorem exitExecutionCost_seq_stop {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (first second : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64)
    (firstRun : StackSemEvaluate.evaluate (first, source) = (some result, middle))
    (firstBound : ExitWeightedFlatten first source result (executionCostPrice price first source)) :
    ExitWeightedFlatten (.seq first second) source result (executionCostPrice price (.seq first second) source) := by
  apply (exitWeightedFlatten_seq_stop first second source result
    (executionCostPrice price first source) ⟨middle, firstRun⟩ firstBound).mono
  intro encoded pc
  simp only [executionCostPrice, stackExecutionCost_seq, firstRun]
  omega

/-- An early terminal exit leaves the second subtree uncharged by the executed model. -/
theorem terminalExecutionCost_seq_stop {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (first second : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (firstRun : StackSemEvaluate.evaluate (first, source) = (some result, middle))
    (firstBound : TerminalWeightedFlatten first source result outcome (executionCostPrice price first source)) :
    TerminalWeightedFlatten (.seq first second) source result outcome (executionCostPrice price (.seq first second) source) := by
  apply (terminalWeightedFlatten_seq_stop first second source result outcome
    (executionCostPrice price first source) ⟨middle, firstRun⟩ firstBound).mono
  intro encoded pc
  simp only [executionCostPrice, stackExecutionCost_seq, firstRun]
  omega

#print axioms normalExecutionCost_seq_next
#print axioms exitExecutionCost_seq_next
#print axioms terminalExecutionCost_seq_next
#print axioms exitExecutionCost_seq_stop
#print axioms terminalExecutionCost_seq_stop
end InitECandidate.Runtime.StackToLab
