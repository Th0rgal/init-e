import InitECandidate.Runtime.StackWeightedCallHandlerPrefix
import InitECandidate.Runtime.StackFlattenShape
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- Compose the actual raised callee and reached exception handler, charging only their visited work. -/
theorem terminalWeightedFlatten_call_handler {F : Type}
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handlerProg : HolProg 64) (hs hl : Nat)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyPrice : LabProgHOL 64 → Nat) (handlerPrice : LabProgHOL 64 → Nat → Nat)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hs hl)), bodyPost))
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) (.exception (.loc hs hl))
      (fun encoded _ => bodyPrice encoded))
    (handlerBound : TerminalWeightedFlatten handlerProg bodyPost result outcome handlerPrice) :
    TerminalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source result outcome
      (fun encoded pc => LabToTarget.controlWork 2 encoded pc + callJumpWork dest +
        bodyPrice encoded + handlerPrice encoded (pc + 3 + (stackFlattenShape returnProg).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨afterBody, stepsB, workB, returnHyps, bodyPC, codeB, boundB, traceB⟩ :=
    callHandlerPrefix_weighted source bodyPost returnProg prog link l1 l2 dest handlerProg hs hl
      bodyPrice positive found bodyRun bodyBound flag (some result) post sectionId labelId
      continues breaks start encoded hyps
  obtain ⟨final, stepsR, workR, ffi, codeR, boundR, traceR, terminal⟩ :=
    handlerBound false post sectionId
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL false returnProg sectionId labelId continues breaks).2.2
      continues breaks afterBody encoded returnHyps
  refine ⟨final, stepsB + stepsR, workB + workR, ffi, codeR.trans codeB, ?_, ?_, terminal⟩
  · dsimp only at boundR ⊢
    rw [bodyPC] at boundR
    omega
  · have joined := LabToTarget.weightedMixedTrace_append (traceB.add_clock stepsR) traceR
    simpa only [Nat.add_assoc] using joined


/-- Compose the actual raised callee and reached exception handler, charging only their visited work. -/
theorem exitWeightedFlatten_call_handler {F : Type}
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handlerProg : HolProg 64) (hs hl : Nat)
    (result : StackSemResult 64)
    (bodyPrice : LabProgHOL 64 → Nat) (handlerPrice : LabProgHOL 64 → Nat → Nat)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hs hl)), bodyPost))
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) (.exception (.loc hs hl))
      (fun encoded _ => bodyPrice encoded))
    (handlerBound : ExitWeightedFlatten handlerProg bodyPost result handlerPrice) :
    ExitWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source result
      (fun encoded pc => LabToTarget.controlWork 2 encoded pc + callJumpWork dest +
        bodyPrice encoded + handlerPrice encoded (pc + 3 + (stackFlattenShape returnProg).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨afterBody, stepsB, workB, returnHyps, bodyPC, codeB, boundB, traceB⟩ :=
    callHandlerPrefix_weighted source bodyPost returnProg prog link l1 l2 dest handlerProg hs hl
      bodyPrice positive found bodyRun bodyBound flag (some result) post sectionId labelId
      continues breaks start encoded hyps
  obtain ⟨final, stepsR, workR, related, codeR, destination, boundR, traceR⟩ :=
    handlerBound false post sectionId
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL false returnProg sectionId labelId continues breaks).2.2
      continues breaks afterBody encoded returnHyps
  refine ⟨final, stepsB + stepsR, workB + workR, related, codeR.trans codeB,
    destination, ?_, ?_⟩
  · dsimp only at boundR ⊢
    rw [bodyPC] at boundR
    omega
  · have joined := LabToTarget.weightedMixedTrace_append (traceB.add_clock stepsR) traceR
    simpa only [Nat.add_assoc] using joined

/-- Compose the actual raised callee and reached exception handler, charging only their visited work. -/
theorem normalWeightedFlatten_call_handler {F : Type}
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handlerProg : HolProg 64) (hs hl : Nat)
    (bodyPrice : LabProgHOL 64 → Nat) (handlerPrice : LabProgHOL 64 → Nat → Nat)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hs hl)), bodyPost))
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) (.exception (.loc hs hl))
      (fun encoded _ => bodyPrice encoded))
    (handlerBound : NormalWeightedFlatten handlerProg bodyPost handlerPrice) :
    NormalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source
      (fun encoded pc => LabToTarget.controlWork 2 encoded pc + callJumpWork dest +
        bodyPrice encoded + handlerPrice encoded (pc + 3 + (stackFlattenShape returnProg).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨afterBody, stepsB, workB, returnHyps, bodyPC, codeB, boundB, traceB⟩ :=
    callHandlerPrefix_weighted source bodyPost returnProg prog link l1 l2 dest handlerProg hs hl
      bodyPrice positive found bodyRun bodyBound flag none post sectionId labelId
      continues breaks start encoded hyps
  obtain ⟨final, stepsR, workR, related, pcR, codeR, boundR, traceR⟩ :=
    handlerBound false post sectionId
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL false returnProg sectionId labelId continues breaks).2.2
      continues breaks afterBody encoded returnHyps
  refine ⟨final, stepsB + stepsR, workB + workR, related, ?_, codeR.trans codeB, ?_, ?_⟩
  · rw [stackFlatten_length] at pcR ⊢
    simp only [stackFlattenShape] at pcR ⊢
    rw [bodyPC] at pcR
    omega
  · dsimp only at boundR ⊢
    rw [bodyPC] at boundR
    omega
  · have joined := LabToTarget.weightedMixedTrace_append (traceB.add_clock stepsR) traceR
    simpa only [Nat.add_assoc] using joined

#print axioms terminalWeightedFlatten_call_handler
#print axioms exitWeightedFlatten_call_handler
#print axioms normalWeightedFlatten_call_handler
end InitECandidate.Runtime.StackToLab
