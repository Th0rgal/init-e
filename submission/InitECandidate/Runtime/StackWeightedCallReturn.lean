import InitECandidate.Runtime.StackWeightedCallReturnPrefix
import InitECandidate.Runtime.StackWeightedExit
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

/-- Compose a real returning callee with its reached terminal continuation.
Only visited prelude, callee, and continuation work is added. -/
theorem terminalWeightedFlatten_call_return {F : Type}
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyPrice : LabProgHOL 64 → Nat) (returnPrice : LabProgHOL 64 → Nat → Nat)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), bodyPost))
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) (.result (.loc l1 l2))
      (fun encoded _ => bodyPrice encoded))
    (returnBound : TerminalWeightedFlatten returnProg bodyPost result outcome returnPrice) :
    TerminalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest handler) source result outcome
      (fun encoded pc => LabToTarget.controlWork 2 encoded pc + callJumpWork dest +
        bodyPrice encoded + returnPrice encoded (pc + 2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨afterBody, stepsB, workB, returnHyps, bodyPC, codeB, boundB, traceB⟩ :=
    callReturnPrefix_weighted source bodyPost returnProg prog link l1 l2 dest handler
      bodyPrice positive found bodyRun bodyBound flag (some result) post sectionId labelId
      continues breaks start encoded hyps
  obtain ⟨final, stepsR, workR, ffi, codeR, boundR, traceR, terminal⟩ :=
    returnBound false post sectionId labelId continues breaks afterBody encoded returnHyps
  refine ⟨final, stepsB + stepsR, workB + workR, ffi, codeR.trans codeB, ?_, ?_, terminal⟩
  · dsimp only at boundR ⊢
    rw [bodyPC] at boundR
    omega
  · have joined := LabToTarget.weightedMixedTrace_append (traceB.add_clock stepsR) traceR
    simpa only [Nat.add_assoc] using joined

#print axioms terminalWeightedFlatten_call_return
end InitECandidate.Runtime.StackToLab
