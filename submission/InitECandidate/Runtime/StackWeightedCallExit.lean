import InitECandidate.Runtime.StackWeightedCall
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

/-- A terminal tail call pays its actual entry jump and its reached callee.
The recursive callee budget is uniform in entry PC, not multiplied by ROM size. -/
theorem exitWeightedFlatten_call_tail {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (dest : Nat ⊕ Nat) (prog : HolProg 64)
    (result : StackSemResult 64)
    (bodyPrice : LabProgHOL 64 → Nat)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest source.regs source.code = some prog)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock source)
      result (fun encoded _ => bodyPrice encoded)) :
    ExitWeightedFlatten (.call none dest none) source result
      (fun encoded _ => callJumpWork dest + bodyPrice encoded) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  have fetch : asmFetchAux start.pc start.code = some (compileJumpHOL dest) :=
    fetchSingle (Prelude.notIsLabelCompileJump dest)
      (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed)
  rw [StackSemEvaluate.evaluate_call, found] at evaluated
  simp only at evaluated
  rw [if_neg positive, StackSemEvaluateClock.fixClockEvaluate] at evaluated
  rcases bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock source) with ⟨bodyResult, bodyPost⟩
  rw [bodyRun] at evaluated
  simp only at evaluated
  by_cases bad : StackSemControl.badFunReturn bodyResult = true
  · rw [if_pos bad] at evaluated
    exact False.elim (nonerror (Prod.mk.inj evaluated).1.symm)
  rw [if_neg bad] at evaluated
  have resultEq := (Prod.mk.inj evaluated).1
  have postEq := (Prod.mk.inj evaluated).2
  subst bodyPost
  rw [resultEq] at bodyRun
  obtain ⟨calleeSection, pc, lookup, entry, calleeArgs, calleeInstalled, calleeRel, jump⟩ :=
    compileJumpEnter_weighted encoded (fun r v h => InstCorrect.regOfLookup related h)
      related positive fetch found
  let middle := {start with pc := pc, clock := start.clock - 1}
  obtain ⟨final, steps, work, finalRelated, code, destination, bounded, trace⟩ :=
    bodyBound true post calleeSection (StackAlloc.nextLabHOL prog 2) [] [] middle encoded
      ⟨bodyRun, nonerror, calleeRel, calleeArgs, calleeInstalled, by simp [middle, entry]⟩
  refine ⟨final, steps, callJumpWork dest + work, finalRelated, code, ?_, by dsimp only at bounded ⊢; omega, ?_⟩
  · unfold WeightedExitDestination at destination ⊢
    have notBad : ¬StackSemControl.badFunReturn (some result) = true := by
      rwa [resultEq] at bad
    rw [← resultViewIndep notBad calleeSection sectionId [] [] continues breaks]
    exact destination
  · have joined := LabToTarget.weightedMixedTrace_append (jump.add_clock steps) trace
    simpa only [Nat.add_zero] using joined

#print axioms exitWeightedFlatten_call_tail
end InitECandidate.Runtime.StackToLab
