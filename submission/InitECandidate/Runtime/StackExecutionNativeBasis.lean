import InitECandidate.Runtime.StackExecutionCostProps
import InitECandidate.Runtime.StackWeightedLeaves
import InitECandidate.Runtime.StackWeightedExit
import InitECandidate.Runtime.StackWeightedTerminal
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- The executed cost model as the recursive native compiler motive's price.
Only the local operation price depends on the fixed compiled encoding. -/
noncomputable def executionCostPrice {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (p : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    LabProgHOL 64 → Nat → Nat :=
  fun encoded _ => stackExecutionCost (fun p s => price p s encoded) p source

/-- Widen a proved normal prefix price without changing its actual trace. -/
theorem NormalWeightedFlatten.mono {F : Type}
    {p : HolProg 64} {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {small large : LabProgHOL 64 → Nat → Nat}
    (bound : NormalWeightedFlatten p source small) (prices : ∀ encoded pc, small encoded pc ≤ large encoded pc) :
    NormalWeightedFlatten p source large := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨final, steps, work, related, pc, code, budget, trace⟩ :=
    bound flag post sectionId labelId continues breaks start encoded hyps
  exact ⟨final, steps, work, related, pc, code, budget.trans (prices encoded start.pc), trace⟩

/-- Widen a proved control-exit prefix price. -/
theorem ExitWeightedFlatten.mono {F : Type}
    {p : HolProg 64} {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {result : StackSemResult 64} {small large : LabProgHOL 64 → Nat → Nat}
    (bound : ExitWeightedFlatten p source result small) (prices : ∀ encoded pc, small encoded pc ≤ large encoded pc) :
    ExitWeightedFlatten p source result large := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨final, steps, work, related, code, destination, budget, trace⟩ :=
    bound flag post sectionId labelId continues breaks start encoded hyps
  exact ⟨final, steps, work, related, code, destination, budget.trans (prices encoded start.pc), trace⟩

/-- Widen a proved terminal prefix price; terminal overhead stays separate. -/
theorem TerminalWeightedFlatten.mono {F : Type}
    {p : HolProg 64} {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {result : StackSemResult 64} {outcome : HolOutcome} {small large : LabProgHOL 64 → Nat → Nat}
    (bound : TerminalWeightedFlatten p source result outcome small)
    (prices : ∀ encoded pc, small encoded pc ≤ large encoded pc) :
    TerminalWeightedFlatten p source result outcome large := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨final, steps, work, ffi, code, budget, trace, terminal⟩ :=
    bound flag post sectionId labelId continues breaks start encoded hyps
  exact ⟨final, steps, work, ffi, code, budget.trans (prices encoded start.pc), trace, terminal⟩

/-- Skip has no emitted native work, including with a zero local price. -/
theorem normalExecutionCost_skip {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    NormalWeightedFlatten .skip source (executionCostPrice price .skip source) := by
  apply (normalWeightedFlatten_skip source).mono
  intro encoded pc
  exact Nat.zero_le _

/-- The actual opcode/padding bound is the only quantitative premise for
an instruction leaf; the executed Stack cost supplies its native budget. -/
theorem normalExecutionCost_inst {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (instruction : HolInst 64)
    (localPrice : ∀ encoded pc, LabToTarget.LocalCost.instructionWork encoded pc instruction ≤
      price (.inst instruction) source encoded) :
    NormalWeightedFlatten (.inst instruction) source (executionCostPrice price (.inst instruction) source) := by
  apply (normalWeightedFlatten_inst source instruction).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost] using localPrice encoded pc

/-- A successful Halt needs no prefix work; its fixed final instruction
allowance is charged once by native extraction. -/
theorem terminalExecutionCost_halt {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (reg : Nat) (value : BitVec 64)
    (read : StackSemStateOps.getVar reg source = some (.word value)) :
    TerminalWeightedFlatten (.halt reg) source (.halt (.word value))
      (if value = 0 then .success else .resourceLimitHit) (executionCostPrice price (.halt reg) source) := by
  apply (terminalWeightedFlatten_halt source reg value read).mono
  intro encoded pc
  exact Nat.zero_le _

#print axioms NormalWeightedFlatten.mono
#print axioms ExitWeightedFlatten.mono
#print axioms TerminalWeightedFlatten.mono
#print axioms normalExecutionCost_skip
#print axioms normalExecutionCost_inst
#print axioms terminalExecutionCost_halt
end InitECandidate.Runtime.StackToLab
