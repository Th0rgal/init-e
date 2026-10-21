import InitECandidate.Runtime.StackWeightedCall
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

/-- A terminal raw call pays its actual entry jump and reached body, skipping the prologue.
The recursive callee budget is uniform in entry PC, not multiplied by ROM size. -/
theorem terminalWeightedFlatten_rawCall {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (dest : Nat) (prologue prog : HolProg 64)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyPrice : LabProgHOL 64 → Nat)
    (positive : source.clock ≠ 0)
    (found : sptLookup dest source.code = some (.seq prologue prog))
    (bodyBound : TerminalWeightedFlatten prog (StackSemStateOps.decClock source)
      result outcome (fun encoded _ => bodyPrice encoded)) :
    TerminalWeightedFlatten (.rawCall dest) source result outcome
      (fun encoded _ => 2 + bodyPrice encoded) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  have fetch : asmFetchAux start.pc start.code = some (.labAsm (.jump (.lab dest 1)) 0 [] 0) :=
    fetchSingle rfl
      (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed)
  rw [StackSemEvaluate.evaluate_rawCall, found] at evaluated
  simp only [StackSemControl.destSeq] at evaluated
  rw [if_neg positive] at evaluated
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
  obtain ⟨calleeArgs, entryPC, calleeInstalled, entry⟩ := relCode related found
  simp only [StackProps.callArgs] at calleeArgs
  rcases prologueFlat : Flapjack.Compiler.Backend.StackToLab.flattenHOL false prologue dest
      (StackAlloc.nextLabHOL (.seq prologue prog) 2) [] [] with ⟨xs, firstNoReturn, bodyLabel⟩
  rcases bodyFlat : Flapjack.Compiler.Backend.StackToLab.flattenHOL false prog dest bodyLabel [] [] with
      ⟨ys, bodyNoReturn, nextLabel⟩
  have flat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL true (.seq prologue prog)
      dest (StackAlloc.nextLabHOL (.seq prologue prog) 2) [] []).1 =
      appListAppend xs ++ (.label dest 1 0 :: appListAppend ys) := by
    rw [Flapjack.Compiler.Backend.StackToLab.flattenHOL]
    simp [prologueFlat, bodyFlat, appListAppendAppend, appListAppendList]
  rw [flat] at calleeInstalled
  obtain ⟨_, installedRest⟩ := codeInstalledAppendImp _ _ _ _ calleeInstalled
  obtain ⟨bodyLocation, installedBody⟩ := labelAt installedRest
  let bodyPC := entryPC + ((appListAppend xs).filter (fun line => !isLabelHOL line)).length
  let middle := {start with pc := bodyPC, clock := start.clock - 1}
  have relatedM : stateRel (StackSemStateOps.decClock source) middle := StateRel.stateRelDecClock related
  have sourceClock := relClock related
  have jump := jump_update_weighted (decClock start) encoded (.lab dest 1) bodyPC fetch
    (by simpa [getPcValue, decClock, bodyPC] using bodyLocation)
  have enter : LabToTarget.WeightedMixedTrace encoded start middle 2 := by
    simpa [middle, decClock, updPc, show start.clock - 1 + 1 = start.clock by omega] using jump.toMixed
  obtain ⟨final, steps, work, ffi, code, bounded, trace, terminal⟩ :=
    bodyBound false post dest bodyLabel [] [] middle encoded
      ⟨bodyRun, nonerror, relatedM, calleeArgs.2,
        by rw [bodyFlat]; exact installedBody,
        by simp [middle, entry]⟩
  refine ⟨final, steps, 2 + work, ffi, code, by dsimp only at bounded ⊢; omega, ?_, terminal⟩
  have joined := LabToTarget.weightedMixedTrace_append (enter.add_clock steps) trace
  simpa only [Nat.add_zero] using joined

#print axioms terminalWeightedFlatten_rawCall
end InitECandidate.Runtime.StackToLab
