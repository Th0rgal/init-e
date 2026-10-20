import InitECandidate.Runtime.StackExecutionNativeBasis
import InitECandidate.Runtime.StackWeightedJumpLower
import InitECandidate.Runtime.StackWeightedJumpLowerExit
import InitECandidate.Runtime.StackWeightedJumpLowerFallthrough
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- A taken JumpLower adds only its local branch price and reached callee cost. -/
theorem exitExecutionCost_jumpLower_taken {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (regX regY dest : Nat) (x y : BitVec 64)
    (prog : HolProg 64) (result : StackSemResult 64)
    (positive : source.clock ≠ 0)
    (readX : StackSemStateOps.getVar regX source = some (.word x))
    (readY : StackSemStateOps.getVar regY source = some (.word y))
    (chosen : wordCmpHOL .lower x y = true)
    (found : sptLookup dest source.code = some prog)
    (localPrice : ∀ encoded, 3 ≤ price (.jumpLower regX regY dest) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock source) result
      (executionCostPrice price prog (StackSemStateOps.decClock source))) :
    ExitWeightedFlatten (.jumpLower regX regY dest) source result
      (executionCostPrice price (.jumpLower regX regY dest) source) := by
  apply (exitWeightedFlatten_jumpLower_taken source regX regY dest x y prog result
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock source) encoded 0)
    positive readX readY chosen found bodyBound).mono
  intro encoded pc
  have found' : StackSemControl.findCode (.inl dest) source.regs source.code = some prog := by
    simpa [StackSemControl.findCode] using found
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_4]
  simp only [readX, readY, chosen, if_true, positive, if_neg, found', if_false]
  have h := localPrice encoded
  omega

/-- A taken JumpLower adds only its local branch price and reached callee cost. -/
theorem terminalExecutionCost_jumpLower_taken {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (regX regY dest : Nat) (x y : BitVec 64)
    (prog : HolProg 64) (result : StackSemResult 64) (outcome : HolOutcome)
    (positive : source.clock ≠ 0)
    (readX : StackSemStateOps.getVar regX source = some (.word x))
    (readY : StackSemStateOps.getVar regY source = some (.word y))
    (chosen : wordCmpHOL .lower x y = true)
    (found : sptLookup dest source.code = some prog)
    (localPrice : ∀ encoded, 3 ≤ price (.jumpLower regX regY dest) source encoded)
    (bodyBound : TerminalWeightedFlatten prog (StackSemStateOps.decClock source) result outcome
      (executionCostPrice price prog (StackSemStateOps.decClock source))) :
    TerminalWeightedFlatten (.jumpLower regX regY dest) source result outcome
      (executionCostPrice price (.jumpLower regX regY dest) source) := by
  apply (terminalWeightedFlatten_jumpLower_taken source regX regY dest x y prog result outcome
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock source) encoded 0)
    positive readX readY chosen found bodyBound).mono
  intro encoded pc
  have found' : StackSemControl.findCode (.inl dest) source.regs source.code = some prog := by
    simpa [StackSemControl.findCode] using found
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_4]
  simp only [readX, readY, chosen, if_true, positive, if_neg, found', if_false]
  have h := localPrice encoded
  omega

/-- A non-taken JumpLower pays no callee work. -/
theorem normalExecutionCost_jumpLower_fallthrough {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (regX regY dest : Nat) (x y : BitVec 64)
    (readX : StackSemStateOps.getVar regX source = some (.word x))
    (readY : StackSemStateOps.getVar regY source = some (.word y))
    (chosen : wordCmpHOL .lower x y = false)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc ≤
      price (.jumpLower regX regY dest) source encoded) :
    NormalWeightedFlatten (.jumpLower regX regY dest) source
      (executionCostPrice price (.jumpLower regX regY dest) source) := by
  apply (normalWeightedFlatten_jumpLower_fallthrough source regX regY dest x y readX readY chosen).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost, readX, readY, chosen,
    Bool.false_eq_true, if_false] using localPrice encoded pc

#print axioms exitExecutionCost_jumpLower_taken
#print axioms terminalExecutionCost_jumpLower_taken
#print axioms normalExecutionCost_jumpLower_fallthrough
end InitECandidate.Runtime.StackToLab
