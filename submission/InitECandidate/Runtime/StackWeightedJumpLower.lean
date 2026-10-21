import InitECandidate.Runtime.StackWeightedCall
import InitECandidate.Runtime.StackWeightedBranch
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
theorem terminalWeightedFlatten_jumpLower_taken {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (regX regY dest : Nat) (x y : BitVec 64) (prog : HolProg 64)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyPrice : LabProgHOL 64 → Nat)
    (positive : source.clock ≠ 0)
    (readX : StackSemStateOps.getVar regX source = some (.word x))
    (readY : StackSemStateOps.getVar regY source = some (.word y))
    (chosen : wordCmpHOL .lower x y = true)
    (found : sptLookup dest source.code = some prog)
    (bodyBound : TerminalWeightedFlatten prog (StackSemStateOps.decClock source)
      result outcome (fun encoded _ => bodyPrice encoded)) :
    TerminalWeightedFlatten (.jumpLower regX regY dest) source result outcome
      (fun encoded _ => 3 + bodyPrice encoded) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  have fetch : asmFetchAux start.pc start.code =
      some (.labAsm (.jumpCmp .lower regX (.reg regY) (.lab dest 0)) 0 [] 0) :=
    fetchSingle rfl
      (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed)
  rw [StackSemEvaluate.evaluate_jumpLower, readX, readY] at evaluated
  simp only at evaluated
  rw [if_pos chosen] at evaluated
  have found' : StackSemControl.findCode (.inl dest) source.regs source.code = some prog := by
    simpa [StackSemControl.findCode] using found
  rw [found'] at evaluated
  simp only at evaluated
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
  obtain ⟨calleeArgs, pc, calleeInstalled, entry⟩ := relCode related found
  let middle := {start with pc := pc, clock := start.clock - 1}
  have calleeRel : stateRel (StackSemStateOps.decClock source) middle := StateRel.stateRelDecClock related
  have sourceClock := relClock related
  have branchChosen : wordSemWordCmp .lower (start.regs regX) (regImm (.reg regY) start) = some true := by
    simp [regImm, InstCorrect.regOfLookup related readX, InstCorrect.regOfLookup related readY,
      wordSemWordCmp, chosen]
  have branch := branch_taken_update_weighted (decClock start) encoded .lower regX (.reg regY)
    (.lab dest 0) pc fetch branchChosen (by simpa [getPcValue, decClock] using entry)
  have jump : LabToTarget.WeightedMixedTrace encoded start middle 3 := by
    simpa [middle, decClock, updPc, show start.clock - 1 + 1 = start.clock by omega] using branch.toMixed
  obtain ⟨final, steps, work, ffi, code, bounded, trace, terminal⟩ :=
    bodyBound true post dest (StackAlloc.nextLabHOL prog 2) [] [] middle encoded
      ⟨bodyRun, nonerror, calleeRel, calleeArgs, calleeInstalled, by simp [middle, entry]⟩
  refine ⟨final, steps, 3 + work, ffi, code, by dsimp only at bounded ⊢; omega, ?_, terminal⟩
  have joined := LabToTarget.weightedMixedTrace_append (jump.add_clock steps) trace
  simpa only [Nat.add_zero] using joined

#print axioms terminalWeightedFlatten_jumpLower_taken
end InitECandidate.Runtime.StackToLab
