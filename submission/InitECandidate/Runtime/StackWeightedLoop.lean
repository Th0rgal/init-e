import InitECandidate.Runtime.StackWeightedLoopLayout
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Loop
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- The actual final loop iteration: its Break0 jumps directly to the installed
loop exit. Structural Loop/labels add no dynamic native work; the body's break
jump is already charged by its exit proof. -/
theorem normalWeightedFlatten_loop_break {F : Type}
    (body : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (price : LabProgHOL 64 → Nat → Nat)
    (bodyRun : ∃ post, StackSemEvaluate.evaluate (body, source) = (some (.break 0), post))
    (bodyBound : ExitWeightedFlatten body source (.break 0) price) :
    NormalWeightedFlatten (.loop body) source price := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, _, related, args, installed, labels⟩
  obtain ⟨middle, run⟩ := bodyRun
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, run] at evaluated
  simp only [StackSemControl.contLoop, StackSemControl.exitLoop, ↓reduceIte,
    Prod.mk.injEq, true_and, Bool.false_eq_true] at evaluated
  subst post
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  have layout := weightedLoopLayout_of_installed body flag sectionId labelId continues breaks start installed labels
  obtain ⟨final, steps, work, finalRelated, code, destination, bound, trace⟩ :=
    bodyBound false middle sectionId (labelId + 2) (labelId :: continues)
      ((labelId + 1) :: breaks) start encoded
      ⟨run, by simp, related, args, layout.bodyInstalled, layout.labels⟩
  have finalPc : final.pc = start.pc + weightedLoopBodyLength body sectionId labelId continues breaks + 1 := by
    simp only [WeightedExitDestination, resultView,
      Flapjack.Compiler.Backend.StackToLab.findLabHOL, List.getElem?_cons_zero,
      Option.getD_some, code] at destination
    exact (Option.some.inj (layout.exit.symm.trans destination)).symm
  exact ⟨final, steps, work, finalRelated, by rw [layout.length]; omega, code, bound, trace⟩

/-- One actual normal body completion and its back jump compose with the
next iteration. The jump consumes the original semantic clock tick; its native
work is charged separately as two instructions, with no depth multiplier. -/
theorem normalWeightedFlatten_loop_step {F : Type}
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyPrice restPrice : LabProgHOL 64 → Nat → Nat)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (none, middle))
    (clock : middle.clock ≠ 0)
    (bodyBound : NormalWeightedFlatten body source bodyPrice)
    (restBound : NormalWeightedFlatten (.loop body) (StackSemStateOps.decClock middle) restPrice) :
    NormalWeightedFlatten (.loop body) source
      (fun encoded pc => bodyPrice encoded pc + 2 + restPrice encoded pc) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, _, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, bodyRun] at evaluated
  simp only [StackSemControl.contLoop, ↓reduceIte, clock] at evaluated
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  have layout := weightedLoopLayout_of_installed body flag sectionId labelId continues breaks start installed labels
  obtain ⟨mid, steps1, work1, midRelated, pc1, code1, bound1, trace1⟩ :=
    bodyBound false middle sectionId (labelId + 2) (labelId :: continues)
      ((labelId + 1) :: breaks) start encoded
      ⟨bodyRun, by simp, related, args, layout.bodyInstalled, layout.labels⟩
  have pc1' : mid.pc = start.pc + weightedLoopBodyLength body sectionId labelId continues breaks := pc1
  let reenter := {mid with pc := start.pc, clock := mid.clock - 1}
  have midClock : mid.clock ≠ 0 := by rw [relClock midRelated]; exact clock
  have fetch : asmFetchAux mid.pc mid.code = some (.labAsm (.jump (.lab sectionId labelId)) 0 [] 0) := by
    rw [pc1', code1]; exact layout.back
  have destination : getPcValue (.lab sectionId labelId) mid = some start.pc := by
    simpa only [getPcValue, code1] using layout.entry
  have jump : LabToTarget.WeightedInstructionTrace encoded mid reenter 2 := by
    have trace := LabToTarget.WeightedInstructionTrace.jump (code := encoded)
      mid reenter (.lab sectionId labelId) start.pc 0 [] 0 0 midClock
      (by simpa only [asmFetch] using fetch) destination
      (by exact LabToTarget.WeightedInstructionTrace.nil (code := encoded) reenter)
    simpa only [Nat.zero_add] using trace
  have reRelated : stateRel (StackSemStateOps.decClock middle) reenter :=
    StateRel.stateRelDecClock midRelated
  have metadata := weightedTrace_metadata trace1
  have argsRest : StackProps.callArgs (.loop body) reenter.ptrReg reenter.lenReg
      reenter.ptr2Reg reenter.len2Reg reenter.linkReg := by
    simpa only [Flapjack.Compiler.Backend.StackProps.callArgs, reenter, metadata.2.1,
      metadata.2.2.1, metadata.2.2.2.1, metadata.2.2.2.2.1, metadata.2.2.2.2.2] using args
  obtain ⟨final, steps2, work2, finalRelated, finalPc, code2, bound2, trace2⟩ :=
    restBound flag post sectionId labelId continues breaks reenter encoded
      ⟨evaluated, by simp, reRelated, argsRest,
        by simpa only [reenter, code1] using installed,
        by simpa only [reenter, code1] using labels⟩
  have backAndRest := LabToTarget.weightedInstructionTrace_append (jump.add_clock steps2) trace2
  have joined := LabToTarget.weightedInstructionTrace_append (trace1.add_clock steps2) backAndRest
  refine ⟨final, steps1 + steps2, work1 + (2 + work2), finalRelated, ?_, ?_, ?_, ?_⟩
  · simpa only [reenter] using finalPc
  · exact code2.trans code1
  · change work2 ≤ restPrice encoded start.pc at bound2
    change work1 + (2 + work2) ≤ bodyPrice encoded start.pc + 2 + restPrice encoded start.pc
    omega
  · simpa only [Nat.add_assoc] using joined

/-- Continue0 reaches its pending jump without executing it. This loop rule
executes and charges that jump once before the actual next iteration. -/
theorem normalWeightedFlatten_loop_continue {F : Type}
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyPrice restPrice : LabProgHOL 64 → Nat → Nat)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (some (.continue 0), middle))
    (clock : middle.clock ≠ 0)
    (bodyBound : ExitWeightedFlatten body source (.continue 0) bodyPrice)
    (restBound : NormalWeightedFlatten (.loop body) (StackSemStateOps.decClock middle) restPrice) :
    NormalWeightedFlatten (.loop body) source
      (fun encoded pc => bodyPrice encoded pc + 2 + restPrice encoded pc) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, _, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, bodyRun] at evaluated
  simp only [StackSemControl.contLoop, decide_true, ↓reduceIte, clock] at evaluated
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  have layout := weightedLoopLayout_of_installed body flag sectionId labelId continues breaks start installed labels
  obtain ⟨mid, steps1, work1, midRelated, code1, pending, bound1, trace1⟩ :=
    bodyBound false middle sectionId (labelId + 2) (labelId :: continues)
      ((labelId + 1) :: breaks) start encoded
      ⟨bodyRun, by simp, related, args, layout.bodyInstalled, layout.labels⟩
  let reenter := {mid with pc := start.pc, clock := mid.clock - 1}
  have midClock : mid.clock ≠ 0 := by rw [relClock midRelated]; exact clock
  have fetch : asmFetchAux mid.pc mid.code = some (.labAsm (.jump (.lab sectionId labelId)) 0 [] 0) := by
    simp only [WeightedExitDestination, resultView,
      Flapjack.Compiler.Backend.StackToLab.findLabHOL, List.getElem?_cons_zero, Option.getD_some] at pending
    exact fetchSingle rfl pending
  have destination : getPcValue (.lab sectionId labelId) mid = some start.pc := by
    simpa only [getPcValue, code1] using layout.entry
  have jump : LabToTarget.WeightedInstructionTrace encoded mid reenter 2 := by
    have trace := LabToTarget.WeightedInstructionTrace.jump (code := encoded)
      mid reenter (.lab sectionId labelId) start.pc 0 [] 0 0 midClock
      (by simpa only [asmFetch] using fetch) destination
      (by exact LabToTarget.WeightedInstructionTrace.nil (code := encoded) reenter)
    simpa only [Nat.zero_add] using trace
  have reRelated : stateRel (StackSemStateOps.decClock middle) reenter :=
    StateRel.stateRelDecClock midRelated
  have metadata := weightedTrace_metadata trace1
  have argsRest : StackProps.callArgs (.loop body) reenter.ptrReg reenter.lenReg
      reenter.ptr2Reg reenter.len2Reg reenter.linkReg := by
    simpa only [Flapjack.Compiler.Backend.StackProps.callArgs, reenter, metadata.2.1,
      metadata.2.2.1, metadata.2.2.2.1, metadata.2.2.2.2.1, metadata.2.2.2.2.2] using args
  obtain ⟨final, steps2, work2, finalRelated, finalPc, code2, bound2, trace2⟩ :=
    restBound flag post sectionId labelId continues breaks reenter encoded
      ⟨evaluated, by simp, reRelated, argsRest,
        by simpa only [reenter, code1] using installed,
        by simpa only [reenter, code1] using labels⟩
  have backAndRest := LabToTarget.weightedInstructionTrace_append (jump.add_clock steps2) trace2
  have joined := LabToTarget.weightedInstructionTrace_append (trace1.add_clock steps2) backAndRest
  refine ⟨final, steps1 + steps2, work1 + (2 + work2), finalRelated, ?_, ?_, ?_, ?_⟩
  · simpa only [reenter] using finalPc
  · exact code2.trans code1
  · change work2 ≤ restPrice encoded start.pc at bound2
    change work1 + (2 + work2) ≤ bodyPrice encoded start.pc + 2 + restPrice encoded start.pc
    omega
  · simpa only [Nat.add_assoc] using joined


#print axioms normalWeightedFlatten_loop_continue
#print axioms normalWeightedFlatten_loop_step
#print axioms normalWeightedFlatten_loop_break
end InitECandidate.Runtime.StackToLab
