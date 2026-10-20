import InitECandidate.Runtime.StackExecutionNativeBasis
import InitECandidate.Runtime.StackWeightedCallReturn
import InitECandidate.Runtime.StackWeightedCallReturnControl
import InitECandidate.Runtime.StackWeightedCallReturnJoin
import InitECandidate.Runtime.StackWeightedCallHandler
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- Exact executed-cost decomposition of a reached returning callee, before
dispatching its actual result to the return or exception continuation. -/
theorem executionCostPrice_call {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg 64 × Nat × Nat)) (bodyResult : Option (StackSemResult 64))
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (bodyResult, bodyPost))
    (encoded : LabProgHOL 64) (pc : Nat) :
    executionCostPrice price (.call (some (returnProg, link, l1, l2)) dest handler) source encoded pc =
      executionCostPrice price prog (StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0 +
      selectedContinuationBudget bodyResult l1 l2 handler
        (executionCostPrice price returnProg bodyPost encoded 0)
        (match handler with | none => 0 | some (hp, _, _) => executionCostPrice price hp bodyPost encoded 0) +
      price (.call (some (returnProg, link, l1, l2)) dest handler) source encoded := by
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_7, if_neg positive, found]
  dsimp only
  rw [StackSemEvaluateClock.fixClockEvaluate, bodyRun]
  cases handler with
  | none => rfl
  | some packet => rcases packet with ⟨hp, hs, hl⟩; rfl

/-- The actual return continuation's normal trace is bounded by the executed call cost. -/
theorem normalExecutionCost_call_return {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), bodyPost))
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 2 encoded pc + callJumpWork dest + 2 ≤
      price (.call (some (returnProg, link, l1, l2)) dest handler) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) (.result (.loc l1 l2))
      (executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))))
    (nextBound : NormalWeightedFlatten returnProg bodyPost (executionCostPrice price returnProg bodyPost)) :
    NormalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest handler) source
      (executionCostPrice price (.call (some (returnProg, link, l1, l2)) dest handler) source) := by
  cases handler with
  | none =>
    apply (normalWeightedFlatten_call_return source bodyPost returnProg prog link l1 l2 dest
      (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0)
      (executionCostPrice price returnProg bodyPost) positive found bodyRun bodyBound nextBound).mono
    intro encoded pc
    rw [executionCostPrice_call price source bodyPost returnProg prog link l1 l2 dest none _ positive found bodyRun encoded pc]
    simp only [selectedContinuationBudget, ↓reduceIte]
    have h := localPrice encoded pc
    dsimp only [executionCostPrice] at h ⊢
    omega
  | some packet =>
    rcases packet with ⟨handlerProg, hs, hl⟩
    apply (normalWeightedFlatten_call_return_handler source bodyPost returnProg prog link l1 l2 dest
      handlerProg hs hl
      (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0)
      (executionCostPrice price returnProg bodyPost) positive found bodyRun bodyBound nextBound).mono
    intro encoded pc
    rw [executionCostPrice_call price source bodyPost returnProg prog link l1 l2 dest
      (some (handlerProg, hs, hl)) _ positive found bodyRun encoded pc]
    simp only [selectedContinuationBudget, ↓reduceIte]
    have h := localPrice encoded pc
    dsimp only [executionCostPrice] at h ⊢
    omega

/-- The actual return continuation's exit trace is bounded by the executed call cost. -/
theorem exitExecutionCost_call_return {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (result : StackSemResult 64)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), bodyPost))
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 2 encoded pc + callJumpWork dest + 2 ≤
      price (.call (some (returnProg, link, l1, l2)) dest handler) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) (.result (.loc l1 l2))
      (executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))))
    (nextBound : ExitWeightedFlatten returnProg bodyPost result (executionCostPrice price returnProg bodyPost)) :
    ExitWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest handler) source result
      (executionCostPrice price (.call (some (returnProg, link, l1, l2)) dest handler) source) := by
  apply (exitWeightedFlatten_call_return source bodyPost returnProg prog link l1 l2 dest handler result
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0)
    (executionCostPrice price returnProg bodyPost) positive found bodyRun bodyBound nextBound).mono
  intro encoded pc
  rw [executionCostPrice_call price source bodyPost returnProg prog link l1 l2 dest handler _ positive found bodyRun encoded pc]
  simp only [selectedContinuationBudget, ↓reduceIte]
  have h := localPrice encoded pc
  dsimp only [executionCostPrice] at h ⊢
  omega

/-- The actual return continuation's terminal trace is bounded by the executed call cost. -/
theorem terminalExecutionCost_call_return {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (result : StackSemResult 64) (outcome : HolOutcome)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), bodyPost))
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 2 encoded pc + callJumpWork dest + 2 ≤
      price (.call (some (returnProg, link, l1, l2)) dest handler) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) (.result (.loc l1 l2))
      (executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))))
    (nextBound : TerminalWeightedFlatten returnProg bodyPost result outcome (executionCostPrice price returnProg bodyPost)) :
    TerminalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest handler) source result outcome
      (executionCostPrice price (.call (some (returnProg, link, l1, l2)) dest handler) source) := by
  apply (terminalWeightedFlatten_call_return source bodyPost returnProg prog link l1 l2 dest handler result outcome
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0)
    (executionCostPrice price returnProg bodyPost) positive found bodyRun bodyBound nextBound).mono
  intro encoded pc
  rw [executionCostPrice_call price source bodyPost returnProg prog link l1 l2 dest handler _ positive found bodyRun encoded pc]
  simp only [selectedContinuationBudget, ↓reduceIte]
  have h := localPrice encoded pc
  dsimp only [executionCostPrice] at h ⊢
  omega

/-- The actual handler continuation's normal trace is bounded by the executed call cost. -/
theorem normalExecutionCost_call_handler {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handlerProg : HolProg 64) (hs hl : Nat)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hs hl)), bodyPost))
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 2 encoded pc + callJumpWork dest + 2 ≤
      price (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) (.exception (.loc hs hl))
      (executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))))
    (nextBound : NormalWeightedFlatten handlerProg bodyPost (executionCostPrice price handlerProg bodyPost)) :
    NormalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source
      (executionCostPrice price (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source) := by
  apply (normalWeightedFlatten_call_handler source bodyPost returnProg prog link l1 l2 dest handlerProg hs hl
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0)
    (executionCostPrice price handlerProg bodyPost) positive found bodyRun bodyBound nextBound).mono
  intro encoded pc
  rw [executionCostPrice_call price source bodyPost returnProg prog link l1 l2 dest (some (handlerProg, hs, hl)) _ positive found bodyRun encoded pc]
  simp only [selectedContinuationBudget, ↓reduceIte]
  have h := localPrice encoded pc
  dsimp only [executionCostPrice] at h ⊢
  omega

/-- The actual handler continuation's exit trace is bounded by the executed call cost. -/
theorem exitExecutionCost_call_handler {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handlerProg : HolProg 64) (hs hl : Nat)
    (result : StackSemResult 64)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hs hl)), bodyPost))
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 2 encoded pc + callJumpWork dest + 2 ≤
      price (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) (.exception (.loc hs hl))
      (executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))))
    (nextBound : ExitWeightedFlatten handlerProg bodyPost result (executionCostPrice price handlerProg bodyPost)) :
    ExitWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source result
      (executionCostPrice price (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source) := by
  apply (exitWeightedFlatten_call_handler source bodyPost returnProg prog link l1 l2 dest handlerProg hs hl result
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0)
    (executionCostPrice price handlerProg bodyPost) positive found bodyRun bodyBound nextBound).mono
  intro encoded pc
  rw [executionCostPrice_call price source bodyPost returnProg prog link l1 l2 dest (some (handlerProg, hs, hl)) _ positive found bodyRun encoded pc]
  simp only [selectedContinuationBudget, ↓reduceIte]
  have h := localPrice encoded pc
  dsimp only [executionCostPrice] at h ⊢
  omega

/-- The actual handler continuation's terminal trace is bounded by the executed call cost. -/
theorem terminalExecutionCost_call_handler {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handlerProg : HolProg 64) (hs hl : Nat)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hs hl)), bodyPost))
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 2 encoded pc + callJumpWork dest + 2 ≤
      price (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) (.exception (.loc hs hl))
      (executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))))
    (nextBound : TerminalWeightedFlatten handlerProg bodyPost result outcome (executionCostPrice price handlerProg bodyPost)) :
    TerminalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source result outcome
      (executionCostPrice price (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source) := by
  apply (terminalWeightedFlatten_call_handler source bodyPost returnProg prog link l1 l2 dest handlerProg hs hl result outcome
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0)
    (executionCostPrice price handlerProg bodyPost) positive found bodyRun bodyBound nextBound).mono
  intro encoded pc
  rw [executionCostPrice_call price source bodyPost returnProg prog link l1 l2 dest (some (handlerProg, hs, hl)) _ positive found bodyRun encoded pc]
  simp only [selectedContinuationBudget, ↓reduceIte]
  have h := localPrice encoded pc
  dsimp only [executionCostPrice] at h ⊢
  omega

#print axioms normalExecutionCost_call_return
#print axioms exitExecutionCost_call_return
#print axioms terminalExecutionCost_call_return
#print axioms normalExecutionCost_call_handler
#print axioms exitExecutionCost_call_handler
#print axioms terminalExecutionCost_call_handler
#print axioms executionCostPrice_call
end InitECandidate.Runtime.StackToLab
