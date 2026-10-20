import InitECandidate.Runtime.StackWeightedLoop
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


/-- Actual reentry rules when a later iteration propagates a nonhalting control exit. -/
theorem exitWeightedFlatten_loop_step {F : Type}
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (exit : StackSemResult 64)
    (bodyPrice restPrice : LabProgHOL 64 → Nat → Nat)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (none, middle))
    (clock : middle.clock ≠ 0)
    (bodyBound : NormalWeightedFlatten body source bodyPrice)
    (restBound : ExitWeightedFlatten (.loop body) (StackSemStateOps.decClock middle) exit restPrice) :
    ExitWeightedFlatten (.loop body) source exit
      (fun encoded pc => bodyPrice encoded pc + 2 + restPrice encoded pc) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
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
  obtain ⟨final, steps2, work2, finalRelated, code2, destination2, bound2, trace2⟩ :=
    restBound flag post sectionId labelId continues breaks reenter encoded
      ⟨evaluated, nonerror, reRelated, argsRest,
        by simpa only [reenter, code1] using installed,
        by simpa only [reenter, code1] using labels⟩
  have backAndRest := LabToTarget.weightedInstructionTrace_append (jump.add_clock steps2) trace2
  have joined := LabToTarget.weightedInstructionTrace_append (trace1.add_clock steps2) backAndRest
  refine ⟨final, steps1 + steps2, work1 + (2 + work2), finalRelated, code2.trans code1, destination2, ?_, ?_⟩
  · change work2 ≤ restPrice encoded start.pc at bound2
    change work1 + (2 + work2) ≤ bodyPrice encoded start.pc + 2 + restPrice encoded start.pc
    omega
  · simpa only [Nat.add_assoc] using joined

theorem exitWeightedFlatten_loop_continue {F : Type}
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (exit : StackSemResult 64)
    (bodyPrice restPrice : LabProgHOL 64 → Nat → Nat)
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (some (.continue 0), middle))
    (clock : middle.clock ≠ 0)
    (bodyBound : ExitWeightedFlatten body source (.continue 0) bodyPrice)
    (restBound : ExitWeightedFlatten (.loop body) (StackSemStateOps.decClock middle) exit restPrice) :
    ExitWeightedFlatten (.loop body) source exit
      (fun encoded pc => bodyPrice encoded pc + 2 + restPrice encoded pc) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
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
  obtain ⟨final, steps2, work2, finalRelated, code2, destination2, bound2, trace2⟩ :=
    restBound flag post sectionId labelId continues breaks reenter encoded
      ⟨evaluated, nonerror, reRelated, argsRest,
        by simpa only [reenter, code1] using installed,
        by simpa only [reenter, code1] using labels⟩
  have backAndRest := LabToTarget.weightedInstructionTrace_append (jump.add_clock steps2) trace2
  have joined := LabToTarget.weightedInstructionTrace_append (trace1.add_clock steps2) backAndRest
  refine ⟨final, steps1 + steps2, work1 + (2 + work2), finalRelated, code2.trans code1, destination2, ?_, ?_⟩
  · change work2 ≤ restPrice encoded start.pc at bound2
    change work1 + (2 + work2) ≤ bodyPrice encoded start.pc + 2 + restPrice encoded start.pc
    omega
  · simpa only [Nat.add_assoc] using joined


#print axioms exitWeightedFlatten_loop_step
#print axioms exitWeightedFlatten_loop_continue
end InitECandidate.Runtime.StackToLab
