import InitECandidate.Runtime.StackWeightedCallEntry
import InitECandidate.Runtime.StackWeightedExit
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

/-- The shared reached-exception-handler prefix for every handler outcome. Its
hypotheses are the original call evaluation and recursive callee bound. -/
theorem callHandlerPrefix_weighted {F : Type}
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handlerProg : HolProg 64) (hs hl : Nat)
    (bodyPrice : LabProgHOL 64 → Nat)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hs hl)), bodyPost))
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) (.exception (.loc hs hl))
      (fun encoded _ => bodyPrice encoded))
    (flag : Bool) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.call (some (returnProg, link, l1, l2)) dest (some (handlerProg, hs, hl)))
      source flag result post sectionId labelId continues breaks start) :
    ∃ afterBody steps work,
      FlattenHyps handlerProg bodyPost false result post sectionId
        (Flapjack.Compiler.Backend.StackToLab.flattenHOL false returnProg sectionId labelId continues breaks).2.2
        continues breaks afterBody ∧
      afterBody.pc = start.pc + 3 + (stackFlattenShape returnProg).2 ∧ afterBody.code = start.code ∧
      work ≤ LabToTarget.controlWork 2 encoded start.pc + callJumpWork dest + bodyPrice encoded ∧
      LabToTarget.WeightedMixedTrace encoded {start with clock := start.clock + steps} afterBody work := by
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_call] at evaluated
  simp only at evaluated
  rw [found] at evaluated
  simp only at evaluated
  rw [if_neg positive] at evaluated
  have returnRun := callRetEval (rp := returnProg) (handler := some (handlerProg, hs, hl)) bodyRun evaluated
  simp only [ne_eq, not_true_eq_false, if_false] at returnRun
  unfold StackProps.callArgs at args
  simp only at args
  rcases flattened : Flapjack.Compiler.Backend.StackToLab.flattenHOL false returnProg
      sectionId labelId continues breaks with ⟨lines, noReturn, nextLabel⟩
  obtain ⟨rest, flat, restEq⟩ := callRetPrelude (t := flag) (link := link) (l1 := l1) (l2 := l2)
    (dest := dest) (handler := some (handlerProg, hs, hl)) flattened
  have originalInstalled := installed
  rw [flat] at installed
  obtain ⟨fetchA, installed2⟩ := lineAt rfl installed
  obtain ⟨fetchB, installed3⟩ := lineAt (Prelude.notIsLabelCompileJump dest) installed2
  obtain ⟨returnLocation, installed4⟩ := labelAt installed3
  obtain ⟨handlerLines, handlerEnd, _, handlerLocation, installedHandler, _, _, handlerFlat⟩ :=
    callHandlerCode flattened originalInstalled
  have returnLength : ((appListAppend lines).filter (fun line => !isLabelHOL line)).length =
      (stackFlattenShape returnProg).2 := by
    have h := stackFlatten_length returnProg false sectionId labelId continues breaks
    rw [flattened] at h
    exact h
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
  have bodyPC : afterBody.pc = start.pc + 3 + (stackFlattenShape returnProg).2 := by
    have destination : locToPc hs hl afterBody.code = some afterBody.pc := destinationB
    rw [codeB, codeM, handlerLocation] at destination
    rw [returnLength] at destination
    have eq := Option.some.inj destination
    omega
  have metadataB := traceB.metadata
  refine ⟨afterBody, 1 + stepsB,
    LabToTarget.controlWork 2 encoded start.pc + callJumpWork dest + workB,
    ⟨returnRun, nonerror, relatedB, ?_, ?_, ?_⟩,
    bodyPC, codeB.trans codeM, ?_, ?_⟩
  · simpa only [metadataB.2.1, metadataB.2.2.1, metadataB.2.2.2.1,
      metadataB.2.2.2.2.1, metadataB.2.2.2.2.2, metadataM.2.1, metadataM.2.2.1,
      metadataM.2.2.2.1, metadataM.2.2.2.2.1, metadataM.2.2.2.2.2] using args.2.2
  · rw [codeB, codeM]
    simp only [Prod.snd] 
    rw [handlerFlat, bodyPC, ← returnLength]
    convert installedHandler using 1 <;> omega
  · simpa only [codeB, codeM] using labels
  · dsimp only at boundB; omega
  · have joined := LabToTarget.weightedMixedTrace_append (enter.add_clock stepsB) traceB
    simpa only [Nat.add_assoc] using joined

#print axioms callHandlerPrefix_weighted
end InitECandidate.Runtime.StackToLab
