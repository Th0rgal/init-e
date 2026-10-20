import InitECandidate.Runtime.StackToLabBudget
import InitECandidate.Runtime.LabWeightedInstructionTrace

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.RiscV.Target

private theorem weighted_appList {α : Type} (l : List α) : appListAppend (.list l) = l :=
  (appListAppend_thm .nil .nil l).2.1

/-- One actual Stack instruction supplies its own locally weighted label trace.
The original flattening hypotheses prove fetch, nonfailure and the related
successor. The added unit is label simulation clock, not a native cost factor. -/
theorem flatten_instruction_weighted {F : Type}
    (source : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F) (instruction : HolInst 64)
    (flag : Bool) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F) (sectionId labelId : Nat)
    (continues breaks : List Nat) (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.inst instruction) source flag result post sectionId labelId
      continues breaks start) :
    result = none ∧ ∃ final, stateRel post final ∧
      LabToTarget.WeightedInstructionTrace encoded
        { start with clock := start.clock + 1 } final
        (LabToTarget.LocalCost.instructionWork encoded start.pc instruction) := by
  rcases hyps with ⟨evaluated, nonerror, related, _, installed, _⟩
  rw [StackSemEvaluate.evaluate_inst] at evaluated
  have fetch : asmFetchAux start.pc start.code = some (.asm (.asmi (.inst instruction)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL,
      weighted_appList] using installed)
  split at evaluated
  · rename_i source' ran
    simp only [Prod.mk.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    have postRelated := InstCorrect.instCorrect ⟨ran, related⟩
    obtain ⟨samePc, sameCode, sameClock, _, _, _, _, _, _, _, _, _, _⟩ :=
      asmInstConsts instruction start
    have nonfailed := InstCorrect.notFailed postRelated
    have successor : incPc (decClock (asmInst instruction
        { start with clock := start.clock + 1 })) = incPc (asmInst instruction start) := by
      rw [Flapjack.Compiler.Backend.LabProps.asmInstWithClock]
      simp only [incPc, decClock, sameClock, Nat.add_sub_cancel]
    refine ⟨rfl, incPc (asmInst instruction start), postRelated, ?_⟩
    have trace := LabToTarget.WeightedInstructionTrace.step
      (code := encoded) { start with clock := start.clock + 1 }
      (incPc (asmInst instruction start)) instruction [] 0 0 (by simp)
      (by simpa only [asmFetch] using fetch)
      (by simp only [Flapjack.Compiler.Backend.LabProps.asmInstWithClock, nonfailed,
        Bool.false_eq_true, not_false_eq_true])
      (by rw [successor]; exact .nil _)
    simpa only [Nat.zero_add] using trace
  · simp only [Prod.mk.injEq] at evaluated
    exact absurd evaluated.1.symm nonerror

/-- Compose the actual Stack instruction with the local RISC-V simulation.
The budget is the visited instruction's encoding cost and padding, not a ROM
maximum. The oracle tie is advanced for subsequent external operations. -/
theorem flatten_instruction_native {F : Type}
    (source : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (instruction : HolInst 64) (flag : Bool) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.inst instruction) source flag result post sectionId labelId
      continues breaks start)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labs : Spt (Spt Nat)) (base : BitVec 64) (asm : AsmState 64)
    (machine : RiscV.L3.riscv_state)
    (target : mc.target = Compiler.Encoders.RiscV.Target.riscvTarget)
    (encoder : encoderCorrect mc.target)
    (related : Flapjack.Compiler.Backend.LabToTarget.stateRel (mc, encoded, labs, base)
      { start with clock := start.clock + 1 } asm machine)
    (tie : Flapjack.Compiler.Backend.LabToTarget.oracleTie mc machine
      { start with clock := start.clock + 1 }) :
    result = none ∧ ∃ final count native finalAsm,
      stateRel post final ∧
      count ≤ LabToTarget.LocalCost.instructionWork encoded start.pc instruction ∧
      (∀ clock, evaluateTargetHOL mc start.ffi
        (clock + count) machine =
        evaluateTargetHOL
          (shiftInterfer count mc) final.ffi clock native) ∧
      Flapjack.Compiler.Backend.LabToTarget.stateRel
        (shiftInterfer count mc, encoded, labs, base)
        final finalAsm native ∧
      Flapjack.Compiler.Backend.LabToTarget.oracleTie
        (shiftInterfer count mc) native final := by
  obtain ⟨same, final, stackRelated, trace⟩ :=
    flatten_instruction_weighted source instruction flag result post sectionId labelId
      continues breaks start encoded hyps
  obtain ⟨count, native, finalAsm, bound, run, nativeRelated, finalTie⟩ :=
    LabToTarget.weightedInstructionTrace_with_oracle encoded trace mc labs base asm machine
      target encoder related tie
  exact ⟨same, final, count, native, finalAsm, stackRelated, bound, run, nativeRelated, finalTie⟩

#print axioms flatten_instruction_native
#print axioms flatten_instruction_weighted
end InitECandidate.Runtime.StackToLab
