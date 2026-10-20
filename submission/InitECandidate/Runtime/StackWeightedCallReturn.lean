import InitECandidate.Runtime.StackWeightedCallEntry
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
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_call] at evaluated
  simp only at evaluated
  rw [found] at evaluated
  simp only at evaluated
  rw [if_neg positive] at evaluated
  have returnRun := callRetEval (rp := returnProg) (handler := handler) bodyRun evaluated
  simp only [ne_eq, not_true_eq_false, if_false] at returnRun
  unfold StackProps.callArgs at args
  simp only at args
  rcases flattened : Flapjack.Compiler.Backend.StackToLab.flattenHOL false returnProg
      sectionId labelId continues breaks with ⟨lines, noReturn, nextLabel⟩
  obtain ⟨rest, flat, restEq⟩ := callRetPrelude (t := flag) (link := link) (l1 := l1) (l2 := l2)
    (dest := dest) (handler := handler) flattened
  rw [flat] at installed
  obtain ⟨fetchA, installed2⟩ := lineAt rfl installed
  obtain ⟨fetchB, installed3⟩ := lineAt (Prelude.notIsLabelCompileJump dest) installed2
  obtain ⟨returnLocation, installed4⟩ := labelAt installed3
  obtain ⟨installedReturn, _⟩ := codeInstalledAppendImp _ _ _ _ installed4
  obtain ⟨calleeSection, pc, middle, codeM, pcM, relatedM, entry, argsM, installedM, enter⟩ :=
    callEnter_weighted encoded related positive fetchA fetchB (by simpa using returnLocation) found
  have metadataM := enter.metadata
  obtain ⟨afterBody, stepsB, workB, relatedB, codeB, destinationB, boundB, traceB⟩ :=
    bodyBound true bodyPost calleeSection (StackAlloc.nextLabHOL prog 2) [] [] middle encoded
      ⟨bodyRun, by simp, relatedM,
        by simpa only [metadataM.2.1, metadataM.2.2.1, metadataM.2.2.2.1,
          metadataM.2.2.2.2.1, metadataM.2.2.2.2.2] using argsM,
        by rw [pcM, codeM]; exact installedM,
        by simp [codeM, entry]⟩
  have bodyPC : afterBody.pc = start.pc + 2 := by
    have destination : locToPc l1 l2 afterBody.code = some afterBody.pc := destinationB
    rw [codeB, codeM, returnLocation] at destination
    exact (Option.some.inj destination).symm
  have metadataB := traceB.metadata
  obtain ⟨final, stepsR, workR, ffi, codeR, boundR, traceR, terminal⟩ :=
    returnBound false post sectionId labelId continues breaks afterBody encoded
      ⟨returnRun, nonerror, relatedB,
        by simpa only [metadataB.2.1, metadataB.2.2.1, metadataB.2.2.2.1,
          metadataB.2.2.2.2.1, metadataB.2.2.2.2.2, metadataM.2.1, metadataM.2.2.1,
          metadataM.2.2.2.1, metadataM.2.2.2.2.1, metadataM.2.2.2.2.2] using args.1,
        by rw [bodyPC, codeB, codeM, flattened]; simpa only [Nat.add_assoc] using installedReturn,
        by simpa only [codeB, codeM] using labels⟩
  refine ⟨final, 1 + stepsB + stepsR,
    LabToTarget.controlWork 2 encoded start.pc + callJumpWork dest + workB + workR,
    ffi, codeR.trans (codeB.trans codeM), ?_, ?_, terminal⟩
  · dsimp only at boundB boundR ⊢
    rw [bodyPC] at boundR
    omega
  · have first := LabToTarget.weightedMixedTrace_append (enter.add_clock stepsB) traceB
    have all := LabToTarget.weightedMixedTrace_append (first.add_clock stepsR) traceR
    simpa only [Nat.add_assoc] using all

#print axioms terminalWeightedFlatten_call_return
end InitECandidate.Runtime.StackToLab
