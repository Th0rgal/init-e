import InitECandidate.Runtime.StackWeightedCompose
import InitECandidate.Runtime.StackWeightedControl
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- Skip and structural labels emit no native instructions. -/
theorem normalWeightedFlatten_skip {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    NormalWeightedFlatten .skip source (fun _ _ => 0) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  have same := hyps.1
  rw [StackSemEvaluate.evaluate_skip] at same
  have hp := (Prod.mk.inj same).2
  subst post
  refine ⟨start, 0, 0, hyps.2.2.1, ?_, rfl, Nat.le_refl _, ?_⟩
  · simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList]
  · simpa only [Nat.add_zero] using LabToTarget.WeightedMixedTrace.nil (code := encoded) start

/-- Ground the recursive motive directly for a successful literal instruction,
using its actual opcode/padding price and compiler state relation. -/
theorem normalWeightedFlatten_inst {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (instruction : HolInst 64) :
    NormalWeightedFlatten (.inst instruction) source
      (fun encoded pc => LabToTarget.LocalCost.instructionWork encoded pc instruction) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_inst] at evaluated
  split at evaluated
  · rename_i sourcePost ran
    simp only [Prod.mk.injEq, true_and] at evaluated
    subst post
    have fetch : asmFetchAux start.pc start.code = some (.asm (.asmi (.inst instruction)) [] 0) :=
      fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed)
    obtain ⟨finalRelated, trace⟩ := instruction_update_weighted source sourcePost instruction start encoded ran related fetch
    obtain ⟨pc, code, _⟩ := asmInstConsts instruction start
    refine ⟨incPc (asmInst instruction start), 1,
      LabToTarget.LocalCost.instructionWork encoded start.pc instruction, finalRelated, ?_, code,
      Nat.le_refl _, trace.toMixed⟩
    simp [incPc, pc, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList, isLabelHOL]
  · simp at evaluated

/-- Location materialization pays only its own visited encoding and padding. -/
theorem normalWeightedFlatten_locValue {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (reg sectionValue labelValue : Nat) :
    NormalWeightedFlatten (.locValue reg sectionValue labelValue) source
      (fun encoded pc => LabToTarget.controlWork 2 encoded pc) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨_, pc, destination, finalRelated, trace⟩ := flatten_locvalue_weighted source reg sectionValue labelValue
    flag none post sectionId labelId continues breaks start encoded hyps
  refine ⟨incPc (updReg reg (.loc sectionValue labelValue) start), 1,
    LabToTarget.controlWork 2 encoded start.pc, finalRelated, ?_, rfl, Nat.le_refl _, trace.toMixed⟩
  simp [incPc, updReg, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList, isLabelHOL]

/-- Tick consumes an original source clock unit. Its one emitted Skip is
charged once and needs no additional label-clock supply. -/
theorem normalWeightedFlatten_tick {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    NormalWeightedFlatten .tick source
      (fun encoded pc => LabToTarget.LocalCost.instructionWork encoded pc .skip) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_tick] at evaluated
  have clockRel := relClock related
  split_ifs at evaluated with zero
  · simp at evaluated
  · simp only [Prod.mk.injEq, true_and] at evaluated
    subst post
    have fetch : asmFetchAux start.pc start.code = some (.asm (.asmi (.inst .skip)) [] 0) :=
      fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed)
    let final := incPc (decClock start)
    have trace := LabToTarget.WeightedInstructionTrace.step (code := encoded) start final .skip [] 0 0
      (by omega) fetch (by simp only [asmInst, InstCorrect.notFailed related, Bool.false_eq_true, not_false_eq_true]) (.nil final)
    refine ⟨final, 0, LabToTarget.LocalCost.instructionWork encoded start.pc .skip,
      StateRel.stateRelDecClock related, ?_, rfl, Nat.le_refl _, ?_⟩
    · simp [final, incPc, decClock, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList, isLabelHOL]
    · simpa only [Nat.add_zero, Nat.zero_add] using trace.toMixed

#print axioms normalWeightedFlatten_skip
#print axioms normalWeightedFlatten_inst
#print axioms normalWeightedFlatten_locValue
#print axioms normalWeightedFlatten_tick
end InitECandidate.Runtime.StackToLab
