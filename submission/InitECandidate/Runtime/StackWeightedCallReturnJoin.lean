import InitECandidate.Runtime.StackWeightedCallReturnPrefix
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

/-- A normal return continuation executes the two-instruction join jump, skipping the installed handler. -/
theorem normalWeightedFlatten_call_return_handler {F : Type}
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handlerProg : HolProg 64) (hs hl : Nat)
    (bodyPrice : LabProgHOL 64 → Nat) (returnPrice : LabProgHOL 64 → Nat → Nat)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), bodyPost))
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) (.result (.loc l1 l2))
      (fun encoded _ => bodyPrice encoded))
    (returnBound : NormalWeightedFlatten returnProg bodyPost returnPrice) :
    NormalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl))) source
      (fun encoded pc => LabToTarget.controlWork 2 encoded pc + callJumpWork dest +
        bodyPrice encoded + returnPrice encoded (pc + 2) + 2) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  have installed := hyps.2.2.2.2.1
  obtain ⟨afterBody, stepsB, workB, returnHyps, bodyPC, codeB, boundB, traceB⟩ :=
    callReturnPrefix_weighted source bodyPost returnProg prog link l1 l2 dest (some (handlerProg, hs, hl))
      bodyPrice positive found bodyRun bodyBound flag none post sectionId labelId
      continues breaks start encoded hyps
  obtain ⟨afterReturn, stepsR, workR, related, pcR, codeR, boundR, traceR⟩ :=
    returnBound false post sectionId labelId continues breaks afterBody encoded returnHyps
  rcases flattened : Flapjack.Compiler.Backend.StackToLab.flattenHOL false returnProg
      sectionId labelId continues breaks with ⟨lines, noReturn, nextLabel⟩
  obtain ⟨handlerLines, handlerEnd, joinFetch, _, _, endLocation, total, _⟩ :=
    callHandlerCode flattened installed
  rw [flattened] at pcR
  have joinPC : afterReturn.pc = start.pc + 1 + 1 +
      ((appListAppend lines).filter (fun line => !isLabelHOL line)).length := by
    rw [bodyPC] at pcR
    exact pcR
  let endPC := start.pc + 1 + 1 +
    ((appListAppend lines).filter (fun line => !isLabelHOL line)).length + 1 +
    ((appListAppend handlerLines).filter (fun line => !isLabelHOL line)).length
  have jump := jump_update_weighted afterReturn encoded (.lab sectionId handlerEnd) endPC
    (by rw [joinPC, codeR, codeB]; exact joinFetch)
    (by simpa only [getPcValue, codeR, codeB, endPC] using endLocation)
  refine ⟨updPc endPC afterReturn, stepsB + stepsR + 1, workB + workR + 2,
    related, ?_, codeR.trans codeB, ?_, ?_⟩
  · simp only [updPc]
    rw [total]
    dsimp only [endPC]
    omega
  · dsimp only at boundR ⊢
    rw [bodyPC] at boundR
    omega
  · have first := LabToTarget.weightedMixedTrace_append (traceB.add_clock stepsR) traceR
    have all := LabToTarget.weightedMixedTrace_append (first.add_clock 1) jump.toMixed
    simpa only [Nat.add_assoc] using all

#print axioms normalWeightedFlatten_call_return_handler
end InitECandidate.Runtime.StackToLab
