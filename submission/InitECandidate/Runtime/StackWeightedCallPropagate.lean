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

/-- Outcomes that a returning call propagates without running either local
continuation. A raised exception propagates only when no handler is installed. -/
def callResultPropagates (result : StackSemResult 64)
    (handler : Option (HolProg 64 × Nat × Nat)) : Prop :=
  match result with
  | .result _ | .break _ | .continue _ => False
  | .exception _ => handler = none
  | _ => True

/-- Actual terminal callee propagation: return and exception continuations
are unexecuted, so the price adds only entry and callee work. -/
theorem terminalWeightedFlatten_call_propagate {F : Type}
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyPrice : LabProgHOL 64 → Nat)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some result, bodyPost))
    (propagates : callResultPropagates result handler)
    (bodyBound : TerminalWeightedFlatten prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) result outcome
      (fun encoded _ => bodyPrice encoded)) :
    TerminalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest handler) source result outcome
      (fun encoded pc => LabToTarget.controlWork 2 encoded pc + callJumpWork dest + bodyPrice encoded) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_call] at evaluated
  simp only at evaluated
  rw [found] at evaluated
  simp only at evaluated
  rw [if_neg positive] at evaluated
  have propagated := callRetEval (rp := returnProg) (handler := handler) bodyRun evaluated
  have postEq : bodyPost = post := by
    cases handler <;> cases result <;> simp_all [callResultPropagates]
  subst post
  rcases flattened : Flapjack.Compiler.Backend.StackToLab.flattenHOL false returnProg
      sectionId labelId continues breaks with ⟨lines, noReturn, nextLabel⟩
  obtain ⟨rest, flat, _⟩ := callRetPrelude (t := flag) (link := link) (l1 := l1) (l2 := l2)
    (dest := dest) (handler := handler) flattened
  rw [flat] at installed
  obtain ⟨fetchA, installed2⟩ := lineAt rfl installed
  obtain ⟨fetchB, installed3⟩ := lineAt (Prelude.notIsLabelCompileJump dest) installed2
  obtain ⟨returnLocation, _⟩ := labelAt installed3
  obtain ⟨calleeSection, pc, middle, codeM, pcM, relatedM, entry, argsM, installedM, enter⟩ :=
    callEnter_weighted encoded related positive fetchA fetchB (by simpa using returnLocation) found
  have metadataM := enter.metadata
  obtain ⟨final, stepsB, workB, ffi, codeB, boundB, traceB, terminal⟩ :=
    bodyBound true bodyPost calleeSection (StackAlloc.nextLabHOL prog 2) [] [] middle encoded
      ⟨bodyRun, nonerror, relatedM,
        by simpa only [metadataM.2.1, metadataM.2.2.1, metadataM.2.2.2.1,
          metadataM.2.2.2.2.1, metadataM.2.2.2.2.2] using argsM,
        by rw [pcM, codeM]; exact installedM,
        by simp [codeM, entry]⟩
  refine ⟨final, 1 + stepsB,
    LabToTarget.controlWork 2 encoded start.pc + callJumpWork dest + workB,
    ffi, codeB.trans codeM, ?_, ?_, terminal⟩
  · dsimp only at boundB ⊢; omega
  · have joined := LabToTarget.weightedMixedTrace_append (enter.add_clock stepsB) traceB
    simpa only [Nat.add_assoc] using joined

#print axioms terminalWeightedFlatten_call_propagate
end InitECandidate.Runtime.StackToLab
