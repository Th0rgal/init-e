import InitECandidate.Runtime.StackExecutionNativeBasis
import InitECandidate.Runtime.StackWeightedLoopExit
import InitECandidate.Runtime.StackWeightedLoopTerminal
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

private theorem loop_reenter_budget {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (run : StackSemEvaluate.evaluate (body, source) = (result, middle))
    (cont : StackSemControl.contLoop result = true) (clock : middle.clock ≠ 0)
    (localPrice : ∀ encoded, 2 ≤ price (.loop body) source encoded) (encoded : LabProgHOL 64) (pc : Nat) :
    executionCostPrice price body source encoded pc + 2 +
      executionCostPrice price (.loop body) (StackSemStateOps.decClock middle) encoded pc ≤
      executionCostPrice price (.loop body) source encoded pc := by
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_3 (fun p s => price p s encoded) source body,
    StackSemEvaluateClock.fixClockEvaluate, run]
  simp only [cont, Bool.true_and, bne_iff_ne, clock, decide_true, if_true]
  rw [if_pos clock]
  have h := localPrice encoded
  omega

private theorem loop_stop_budget {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (run : StackSemEvaluate.evaluate (body, source) = (result, middle))
    (stopped : StackSemControl.contLoop result = false) (encoded : LabProgHOL 64) (pc : Nat) :
    executionCostPrice price body source encoded pc ≤
      executionCostPrice price (.loop body) source encoded pc := by
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_3 (fun p s => price p s encoded) source body,
    StackSemEvaluateClock.fixClockEvaluate, run]
  simp only [stopped, Bool.false_and, Bool.false_eq_true, if_false]
  omega

/-- Executed loop cost pays the actual reentry once before its later normal outcome. -/
theorem normalExecutionCost_loop_step {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (none, middle))
    (clock : middle.clock ≠ 0)
    (localPrice : ∀ encoded, 2 ≤ price (.loop body) source encoded)
    (bodyBound : NormalWeightedFlatten body source (executionCostPrice price body source))
    (restBound : NormalWeightedFlatten (.loop body) (StackSemStateOps.decClock middle)
      (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))) :
    NormalWeightedFlatten (.loop body) source (executionCostPrice price (.loop body) source) := by
  apply (normalWeightedFlatten_loop_step body source middle
    (executionCostPrice price body source)
    (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))
    bodyRun clock bodyBound restBound).mono
  intro encoded pc
  exact loop_reenter_budget price body source middle _ bodyRun (by simp [StackSemControl.contLoop])
    clock localPrice encoded pc

/-- Executed loop cost pays the actual reentry once before its later normal outcome. -/
theorem normalExecutionCost_loop_continue {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (some (.continue 0), middle))
    (clock : middle.clock ≠ 0)
    (localPrice : ∀ encoded, 2 ≤ price (.loop body) source encoded)
    (bodyBound : ExitWeightedFlatten body source (.continue 0) (executionCostPrice price body source))
    (restBound : NormalWeightedFlatten (.loop body) (StackSemStateOps.decClock middle)
      (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))) :
    NormalWeightedFlatten (.loop body) source (executionCostPrice price (.loop body) source) := by
  apply (normalWeightedFlatten_loop_continue body source middle
    (executionCostPrice price body source)
    (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))
    bodyRun clock bodyBound restBound).mono
  intro encoded pc
  exact loop_reenter_budget price body source middle _ bodyRun (by simp [StackSemControl.contLoop])
    clock localPrice encoded pc

/-- Executed loop cost pays the actual reentry once before its later exit outcome. -/
theorem exitExecutionCost_loop_step {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (none, middle))
    (clock : middle.clock ≠ 0)
    (localPrice : ∀ encoded, 2 ≤ price (.loop body) source encoded)
    (bodyBound : NormalWeightedFlatten body source (executionCostPrice price body source))
    (restBound : ExitWeightedFlatten (.loop body) (StackSemStateOps.decClock middle) result
      (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))) :
    ExitWeightedFlatten (.loop body) source result (executionCostPrice price (.loop body) source) := by
  apply (exitWeightedFlatten_loop_step body source middle result
    (executionCostPrice price body source)
    (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))
    bodyRun clock bodyBound restBound).mono
  intro encoded pc
  exact loop_reenter_budget price body source middle _ bodyRun (by simp [StackSemControl.contLoop])
    clock localPrice encoded pc

/-- Executed loop cost pays the actual reentry once before its later exit outcome. -/
theorem exitExecutionCost_loop_continue {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (some (.continue 0), middle))
    (clock : middle.clock ≠ 0)
    (localPrice : ∀ encoded, 2 ≤ price (.loop body) source encoded)
    (bodyBound : ExitWeightedFlatten body source (.continue 0) (executionCostPrice price body source))
    (restBound : ExitWeightedFlatten (.loop body) (StackSemStateOps.decClock middle) result
      (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))) :
    ExitWeightedFlatten (.loop body) source result (executionCostPrice price (.loop body) source) := by
  apply (exitWeightedFlatten_loop_continue body source middle result
    (executionCostPrice price body source)
    (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))
    bodyRun clock bodyBound restBound).mono
  intro encoded pc
  exact loop_reenter_budget price body source middle _ bodyRun (by simp [StackSemControl.contLoop])
    clock localPrice encoded pc

/-- Executed loop cost pays the actual reentry once before its later terminal outcome. -/
theorem terminalExecutionCost_loop_step {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (none, middle))
    (clock : middle.clock ≠ 0)
    (localPrice : ∀ encoded, 2 ≤ price (.loop body) source encoded)
    (bodyBound : NormalWeightedFlatten body source (executionCostPrice price body source))
    (restBound : TerminalWeightedFlatten (.loop body) (StackSemStateOps.decClock middle) result outcome
      (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))) :
    TerminalWeightedFlatten (.loop body) source result outcome (executionCostPrice price (.loop body) source) := by
  apply (terminalWeightedFlatten_loop_step body source middle result outcome
    (executionCostPrice price body source)
    (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))
    bodyRun clock bodyBound restBound).mono
  intro encoded pc
  exact loop_reenter_budget price body source middle _ bodyRun (by simp [StackSemControl.contLoop])
    clock localPrice encoded pc

/-- Executed loop cost pays the actual reentry once before its later terminal outcome. -/
theorem terminalExecutionCost_loop_continue {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (some (.continue 0), middle))
    (clock : middle.clock ≠ 0)
    (localPrice : ∀ encoded, 2 ≤ price (.loop body) source encoded)
    (bodyBound : ExitWeightedFlatten body source (.continue 0) (executionCostPrice price body source))
    (restBound : TerminalWeightedFlatten (.loop body) (StackSemStateOps.decClock middle) result outcome
      (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))) :
    TerminalWeightedFlatten (.loop body) source result outcome (executionCostPrice price (.loop body) source) := by
  apply (terminalWeightedFlatten_loop_continue body source middle result outcome
    (executionCostPrice price body source)
    (executionCostPrice price (.loop body) (StackSemStateOps.decClock middle))
    bodyRun clock bodyBound restBound).mono
  intro encoded pc
  exact loop_reenter_budget price body source middle _ bodyRun (by simp [StackSemControl.contLoop])
    clock localPrice encoded pc

/-- The final Break0 iteration pays no unexecuted reentry. -/
theorem normalExecutionCost_loop_break {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (some (.break 0), middle))
    (bodyBound : ExitWeightedFlatten body source (.break 0) (executionCostPrice price body source)) :
    NormalWeightedFlatten (.loop body) source (executionCostPrice price (.loop body) source) := by
  apply (normalWeightedFlatten_loop_break body source (executionCostPrice price body source)
    ⟨middle, bodyRun⟩ bodyBound).mono
  intro encoded pc
  exact loop_stop_budget price body source middle _ bodyRun (by simp [StackSemControl.contLoop]) encoded pc

/-- A propagated loop exit exit does not price another iteration. -/
theorem exitExecutionCost_loop_exit {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyResult result : StackSemResult 64)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (some bodyResult, middle))
    (stopped : StackSemControl.contLoop (some bodyResult) = false)
    (exited : StackSemControl.exitLoop (some bodyResult) = some result)
    (bodyBound : ExitWeightedFlatten body source bodyResult (executionCostPrice price body source)) :
    ExitWeightedFlatten (.loop body) source result (executionCostPrice price (.loop body) source) := by
  apply (exitWeightedFlatten_loop_exit body source bodyResult result
    (executionCostPrice price body source) ⟨middle, bodyRun⟩ stopped exited bodyBound).mono
  intro encoded pc
  exact loop_stop_budget price body source middle _ bodyRun stopped encoded pc

/-- A propagated loop terminal exit does not price another iteration. -/
theorem terminalExecutionCost_loop_exit {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyResult result : StackSemResult 64) (outcome : HolOutcome)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (some bodyResult, middle))
    (stopped : StackSemControl.contLoop (some bodyResult) = false)
    (exited : StackSemControl.exitLoop (some bodyResult) = some result)
    (bodyBound : TerminalWeightedFlatten body source bodyResult outcome (executionCostPrice price body source)) :
    TerminalWeightedFlatten (.loop body) source result outcome (executionCostPrice price (.loop body) source) := by
  apply (terminalWeightedFlatten_loop_exit body source bodyResult result outcome
    (executionCostPrice price body source) ⟨middle, bodyRun⟩ stopped exited bodyBound).mono
  intro encoded pc
  exact loop_stop_budget price body source middle _ bodyRun stopped encoded pc

#print axioms normalExecutionCost_loop_step
#print axioms normalExecutionCost_loop_continue
#print axioms exitExecutionCost_loop_step
#print axioms exitExecutionCost_loop_continue
#print axioms terminalExecutionCost_loop_step
#print axioms terminalExecutionCost_loop_continue
#print axioms normalExecutionCost_loop_break
#print axioms exitExecutionCost_loop_exit
#print axioms terminalExecutionCost_loop_exit
end InitECandidate.Runtime.StackToLab
