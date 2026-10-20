import InitECandidate.Runtime.StackWeightedInstruction
import InitECandidate.Runtime.StackToLabCompose
import InitECandidate.Runtime.LabWeightedClock
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Ordinary instructions with the exact sequence shape used by this block. -/
def instructionBlock (instructions : List (HolInst 64)) : HolProg 64 :=
  instructions.foldr (fun instruction rest => .seq (.inst instruction) rest) .skip

/-- All recursive work is explicit. Each leaf premise is the literal single
instruction update, not a whole-program successful-execution oracle. -/
inductive InstructionBlockRun {F : Type} :
    StackSemStateFiniteExact 64 LabToTarget.Config F → List (HolInst 64) →
      StackSemStateFiniteExact 64 LabToTarget.Config F → Prop where
  | nil (s) : InstructionBlockRun s [] s
  | cons {s middle post instruction rest}
      (step : StackSemInst.instHOL instruction s = some middle)
      (tail : InstructionBlockRun middle rest post) :
      InstructionBlockRun s (instruction :: rest) post

theorem InstructionBlockRun.sound {F : Type}
    {s post : StackSemStateFiniteExact 64 LabToTarget.Config F} {instructions : List (HolInst 64)}
    (run : InstructionBlockRun s instructions post) :
    StackSemEvaluate.evaluate (instructionBlock instructions, s) = (none, post) := by
  induction run with
  | nil s => simp only [instructionBlock, List.foldr_nil, StackSemEvaluate.evaluate_skip]
  | cons step tail ih =>
    change StackSemEvaluate.evaluate ((Prog.inst _).seq (instructionBlock _), _) = _
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_inst, step]
    exact ih

theorem instructionBlockRun_of_evaluate {F : Type} (instructions : List (HolInst 64))
    (s post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (evaluated : StackSemEvaluate.evaluate (instructionBlock instructions, s) = (none, post)) :
    InstructionBlockRun s instructions post := by
  induction instructions generalizing s post with
  | nil =>
    simp only [instructionBlock, List.foldr_nil, StackSemEvaluate.evaluate_skip,
      Prod.mk.injEq, true_and] at evaluated
    subst evaluated
    exact .nil s
  | cons instruction rest ih =>
    change StackSemEvaluate.evaluate ((Prog.inst instruction).seq (instructionBlock rest), s) =
      (none, post) at evaluated
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_inst] at evaluated
    cases step : StackSemInst.instHOL instruction s with
    | none => simp only [step, reduceCtorEq, Prod.mk.injEq, false_and] at evaluated
    | some middle =>
      simp only [step] at evaluated
      exact .cons step (ih middle post evaluated)

/-- The actual local native cost of each visited instruction, at its position.
Unlike a leaf-count multiplier this retains opcode and actual padding costs. -/
noncomputable def instructionBlockWork (encoded : LabProgHOL 64) : Nat → List (HolInst 64) → Nat
  | _, [] => 0
  | pc, instruction :: rest => LabToTarget.LocalCost.instructionWork encoded pc instruction +
      instructionBlockWork encoded (pc + 1) rest

/-- Source instruction sequence to the actual weighted label prefix. The
only code premise is installation of its literal ordinary instruction lines. -/
theorem InstructionBlockRun.weighted {F : Type}
    {s post : StackSemStateFiniteExact 64 LabToTarget.Config F} {instructions : List (HolInst 64)}
    (run : InstructionBlockRun s instructions post)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64)
    (related : stateRel s start)
    (installed : codeInstalled start.pc
      (instructions.map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64))) start.code) :
    ∃ final, stateRel post final ∧ final.pc = start.pc + instructions.length ∧
      final.code = start.code ∧
      LabToTarget.WeightedInstructionTrace encoded
        { start with clock := start.clock + instructions.length } final
        (instructionBlockWork encoded start.pc instructions) := by
  induction run generalizing start with
  | nil s =>
    exact ⟨start, related, by simp, rfl, by
      simpa only [List.length_nil, Nat.add_zero, instructionBlockWork] using
        LabToTarget.WeightedInstructionTrace.nil (code := encoded) start⟩
  | @cons s middle post instruction rest step tail ih =>
    simp only [List.map_cons, codeInstalled_cons, isLabelHOL, Bool.false_eq_true,
      if_false] at installed
    have first := instruction_update_weighted s middle instruction start encoded step related
      installed.1
    let next := incPc (asmInst instruction start)
    have nextPc : next.pc = start.pc + 1 := by
      have same := (asmInstConsts instruction start).1
      simpa only [next, incPc] using congrArg (fun n => n + 1) same
    have nextCode : next.code = start.code := (asmInstConsts instruction start).2.1
    obtain ⟨final, finalRelated, finalPc, finalCode, second⟩ := ih next first.1 (by
      rw [nextPc, nextCode]; exact installed.2)
    have firstLift := first.2.add_clock rest.length
    have joined := LabToTarget.weightedInstructionTrace_append firstLift second
    refine ⟨final, finalRelated, ?_, finalCode.trans nextCode, ?_⟩
    · rw [finalPc, nextPc, List.length_cons]; omega
    · simpa only [List.length_cons, instructionBlockWork, nextPc,
        Nat.add_assoc, Nat.add_comm 1, Nat.add_left_comm] using joined

private theorem block_appAppend {α : Type} (a b : AppList α) :
    appListAppend (.append a b) = appListAppend a ++ appListAppend b :=
  (appListAppend_thm a b []).1

private theorem block_appList {α : Type} (lines : List α) :
    appListAppend (.list lines) = lines := (appListAppend_thm .nil .nil lines).2.1

/-- Removing label assertions from the installed pattern keeps every fetched
ordinary line and its exact position. -/
theorem block_installed_without_labels (lines : List (LabLineHOL 64)) (pc : Nat)
    (code : LabProgHOL 64) (installed : codeInstalled pc lines code) :
    codeInstalled pc (lines.filter (fun line => !isLabelHOL line)) code := by
  induction lines generalizing pc with
  | nil => trivial
  | cons line rest ih =>
    rw [codeInstalled_cons] at installed
    by_cases label : isLabelHOL line = true
    · rw [if_pos label] at installed
      simpa only [List.filter_cons, label, Bool.not_true, Bool.false_eq_true, if_false] using
        ih pc installed.2
    · rw [if_neg label] at installed
      have notLabel : isLabelHOL line = false := Bool.eq_false_iff.mpr label
      simp only [List.filter_cons, notLabel, Bool.not_false, ↓reduceIte, codeInstalled_cons]
      exact ⟨installed.1, ih (pc + 1) installed.2⟩

/-- Flattening this actual Stack program emits precisely its instructions;
sequence join labels cost no instructions and do not change the next label. -/
theorem flatten_instructionBlock_lines (instructions : List (HolInst 64)) (flag : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat) :
    let compiled := Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (instructionBlock instructions) sectionId labelId continues breaks
    compiled.2.2 = labelId ∧
      (appListAppend compiled.1).filter (fun line => !isLabelHOL line) =
        instructions.map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64)) := by
  induction instructions generalizing flag labelId with
  | nil =>
    simp only [instructionBlock, List.foldr_nil, Flapjack.Compiler.Backend.StackToLab.flattenHOL,
      block_appList, List.filter_nil, List.map_nil, and_self]
  | cons instruction rest ih =>
    have tail := ih false labelId
    change (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      ((Prog.inst instruction).seq (instructionBlock rest)) sectionId labelId continues breaks).2.2 =
        labelId ∧
      (appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
        ((Prog.inst instruction).seq (instructionBlock rest)) sectionId labelId continues breaks).1).filter
          (fun line => !isLabelHOL line) =
        (instruction :: rest).map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64))
    simp only [Flapjack.Compiler.Backend.StackToLab.flattenHOL]
    cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte, block_appAppend, block_appList,
      List.filter_append, List.filter_cons, isLabelHOL, Bool.not_false, Bool.not_true,
      List.filter_nil, Bool.false_eq_true, ↓reduceIte, List.singleton_append, List.nil_append,
      List.cons_append, List.map_cons, tail.1, tail.2, true_and]
    all_goals exact (congrArg (List.cons (.asm (.asmi (.inst instruction)) [] 0 : LabLineHOL 64)) tail.2)

/-- Whole ordinary block transfer under the original flattening hypotheses.
Its cost is the sum of actual opcode/padding costs at consecutive positions;
no whole-program maximum or instruction-count multiplier is introduced. -/
theorem flatten_instructionBlock_weighted {F : Type} (instructions : List (HolInst 64))
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (flag : Bool) (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.FlattenHyps
      (instructionBlock instructions) source flag none post sectionId labelId continues breaks start) :
    ∃ final, stateRel post final ∧ final.pc = start.pc + instructions.length ∧
      final.code = start.code ∧ LabToTarget.WeightedInstructionTrace encoded
        { start with clock := start.clock + instructions.length } final
        (instructionBlockWork encoded start.pc instructions) := by
  rcases hyps with ⟨evaluated, _, related, _, installed, _⟩
  have run := instructionBlockRun_of_evaluate instructions source post evaluated
  have bare := block_installed_without_labels _ _ _ installed
  rw [(flatten_instructionBlock_lines instructions flag sectionId labelId continues breaks).2]
    at bare
  exact run.weighted start encoded related bare

/-- Native execution of the actual compiled ordinary block. The bound sums
its visited opcode expansions and padding, and the final relations permit the
next compiled block or external operation to follow. -/
theorem flatten_instructionBlock_native {F : Type} (instructions : List (HolInst 64))
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (flag : Bool) (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.FlattenHyps
      (instructionBlock instructions) source flag none post sectionId labelId continues breaks start)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (labs : Spt (Spt Nat))
    (base : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : Flapjack.Compiler.Backend.LabToTarget.stateRel (mc, encoded, labs, base)
      { start with clock := start.clock + instructions.length } asm machine)
    (tie : Flapjack.Compiler.Backend.LabToTarget.oracleTie mc machine
      { start with clock := start.clock + instructions.length }) :
    ∃ final count native finalAsm, stateRel post final ∧
      final.pc = start.pc + instructions.length ∧ final.code = start.code ∧
      count ≤ instructionBlockWork encoded start.pc instructions ∧
      (∀ clock, evaluateTargetHOL mc start.ffi (clock + count) machine =
        evaluateTargetHOL (shiftInterfer count mc) final.ffi clock native) ∧
      Flapjack.Compiler.Backend.LabToTarget.stateRel
        (shiftInterfer count mc, encoded, labs, base) final finalAsm native ∧
      Flapjack.Compiler.Backend.LabToTarget.oracleTie (shiftInterfer count mc) native final := by
  obtain ⟨final, stackRelated, pc, code, trace⟩ := flatten_instructionBlock_weighted instructions
    source post flag sectionId labelId continues breaks start encoded hyps
  obtain ⟨count, native, finalAsm, bound, run, nativeRelated, finalTie⟩ :=
    LabToTarget.weightedInstructionTrace_with_oracle encoded trace mc labs base asm machine
      target encoder related tie
  exact ⟨final, count, native, finalAsm, stackRelated, pc, code, bound, run, nativeRelated,
    finalTie⟩

#print axioms flatten_instructionBlock_native
#print axioms flatten_instructionBlock_weighted
#print axioms flatten_instructionBlock_lines
#print axioms block_installed_without_labels
#print axioms InstructionBlockRun.sound
#print axioms instructionBlockRun_of_evaluate
#print axioms InstructionBlockRun.weighted
end InitECandidate.Runtime.StackToLab
