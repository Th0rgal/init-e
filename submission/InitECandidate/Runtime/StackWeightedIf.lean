import InitECandidate.Runtime.StackWeightedBranch
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- The true arm of the ACTUAL compiled two-block conditional. The other arm
only determines a code location; none of its instruction costs are charged. -/
theorem flatten_instructionBlock_if_true_weighted {F : Type}
    (yes no : List (HolInst 64)) (yesNonempty : yes ≠ []) (noNonempty : no ≠ [])
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source post : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (flag : Bool) (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.ite cmp reg operand (instructionBlock yes) (instructionBlock no))
      source flag none post sectionId labelId continues breaks start)
    (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true) :
    ∃ final, stateRel post final ∧
      final.pc = start.pc + 2 + no.length + yes.length ∧ final.code = start.code ∧
      LabToTarget.WeightedInstructionTrace encoded
        { start with clock := start.clock + 1 + yes.length } final
        (3 + instructionBlockWork encoded (start.pc + 2 + no.length) yes) := by
  rcases hyps with ⟨evaluated, _, related, _, installed, _⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have sourceRun := instructionBlockRun_of_evaluate yes source post evaluated
  rw [flatten_instructionBlock_if_lines yes no yesNonempty noNonempty cmp reg operand
    flag sectionId labelId continues breaks] at installed
  obtain ⟨fetch, rest⟩ := lineAt rfl installed
  obtain ⟨installedNo, rest2⟩ := codeInstalledAppendImp _ _ _ _ rest
  obtain ⟨joinFetch, rest3⟩ := lineAt rfl rest2
  obtain ⟨destination, rest4⟩ := labelAt rest3
  obtain ⟨installedYes, _⟩ := codeInstalledAppendImp _ _ _ _ rest4
  have noLength : ((no.map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64))).filter
      (fun line => !isLabelHOL line)).length = no.length := by
    simp [List.filter_map, isLabelHOL]
  simp only [noLength] at destination installedYes
  let branchStart := updPc (start.pc + 1 + no.length + 1) start
  obtain ⟨final, finalRelated, finalPc, finalCode, child⟩ := sourceRun.weighted branchStart encoded
    related installedYes
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some true := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have first := branch_taken_update_weighted start encoded cmp reg operand (.lab sectionId labelId)
    (start.pc + 1 + no.length + 1) fetch condition destination
  have joined := LabToTarget.weightedInstructionTrace_append (first.add_clock yes.length) child
  refine ⟨final, finalRelated, ?_, finalCode, ?_⟩
  · dsimp only [branchStart, updPc] at finalPc
    omega
  · have pcEq : start.pc + 1 + no.length + 1 = start.pc + 2 + no.length := by omega
    dsimp only [branchStart, updPc] at joined
    rw [pcEq] at joined
    simpa only [Nat.add_assoc] using joined

/-- The false arm executes its ordinary block and the compiler's one join
jump. The true arm has no dynamic cost on this path. -/
theorem flatten_instructionBlock_if_false_weighted {F : Type}
    (yes no : List (HolInst 64)) (yesNonempty : yes ≠ []) (noNonempty : no ≠ [])
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source post : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (flag : Bool) (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.ite cmp reg operand (instructionBlock yes) (instructionBlock no))
      source flag none post sectionId labelId continues breaks start)
    (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false) :
    ∃ final, stateRel post final ∧
      final.pc = start.pc + 2 + no.length + yes.length ∧ final.code = start.code ∧
      LabToTarget.WeightedInstructionTrace encoded
        { start with clock := start.clock + 1 + no.length + 1 } final
        (LabToTarget.controlWork 3 encoded start.pc +
          instructionBlockWork encoded (start.pc + 1) no + 2) := by
  rcases hyps with ⟨evaluated, _, related, _, installed, _⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have sourceRun := instructionBlockRun_of_evaluate no source post evaluated
  rw [flatten_instructionBlock_if_lines yes no yesNonempty noNonempty cmp reg operand
    flag sectionId labelId continues breaks] at installed
  obtain ⟨fetch, rest⟩ := lineAt rfl installed
  obtain ⟨installedNo, rest2⟩ := codeInstalledAppendImp _ _ _ _ rest
  obtain ⟨joinFetch, rest3⟩ := lineAt rfl rest2
  obtain ⟨destination, rest4⟩ := labelAt rest3
  obtain ⟨installedYes, rest5⟩ := codeInstalledAppendImp _ _ _ _ rest4
  obtain ⟨joinDestination, _⟩ := labelAt rest5
  have noLength : ((no.map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64))).filter
      (fun line => !isLabelHOL line)).length = no.length := by simp [List.filter_map, isLabelHOL]
  have yesLength : ((yes.map (fun i => (.asm (.asmi (.inst i)) [] 0 : LabLineHOL 64))).filter
      (fun line => !isLabelHOL line)).length = yes.length := by simp [List.filter_map, isLabelHOL]
  simp only [noLength, yesLength] at joinFetch joinDestination
  obtain ⟨middle, middleRelated, middlePc, middleCode, child⟩ := sourceRun.weighted (incPc start) encoded
    related installedNo
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some false := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have first := branch_fallthrough_update_weighted start encoded cmp reg operand
    (.lab sectionId labelId) fetch condition
  have childLift : LabToTarget.WeightedInstructionTrace encoded
      { incPc start with clock := (incPc start).clock + (no.length + 1) }
      { middle with clock := middle.clock + 1 }
      (instructionBlockWork encoded (start.pc + 1) no) := by
    simpa only [incPc, Nat.add_assoc] using child.add_clock 1
  have prefixRun := LabToTarget.weightedInstructionTrace_append (first.add_clock (no.length + 1)) childLift
  have lastFetch : asmFetchAux middle.pc middle.code =
      some (.labAsm (.jump (.lab sectionId (labelId + 1))) 0 [] 0) := by
    rw [middlePc, middleCode]
    exact joinFetch
  have lastDestination : getPcValue (.lab sectionId (labelId + 1)) middle =
      some (start.pc + 1 + no.length + 1 + yes.length) := by
    simpa only [getPcValue, middleCode, incPc] using joinDestination
  have last := jump_update_weighted middle encoded (.lab sectionId (labelId + 1))
    (start.pc + 1 + no.length + 1 + yes.length) lastFetch lastDestination
  have joined := LabToTarget.weightedInstructionTrace_append prefixRun last
  refine ⟨updPc (start.pc + 1 + no.length + 1 + yes.length) middle, middleRelated,
    by simp only [updPc]; omega, middleCode, ?_⟩
  simpa only [Nat.add_assoc] using joined

/-- Label-clock supply for the executed arm, separate from native work. -/
def instructionBlockIfClock (yes no : List (HolInst 64)) (chosen : Bool) : Nat :=
  if chosen then 1 + yes.length else 1 + no.length + 1

/-- Actual visited native work of the branch, its selected ordinary arm, and
only the join jump which that arm executes. -/
noncomputable def instructionBlockIfWork (encoded : LabProgHOL 64) (pc : Nat)
    (yes no : List (HolInst 64)) (chosen : Bool) : Nat :=
  if chosen then 3 + instructionBlockWork encoded (pc + 2 + no.length) yes
  else LabToTarget.controlWork 3 encoded pc + instructionBlockWork encoded (pc + 1) no + 2

/-- Complete true/false transfer for this real compiler-produced conditional,
with no work charged for its unexecuted arm. -/
theorem flatten_instructionBlock_if_weighted {F : Type}
    (yes no : List (HolInst 64)) (yesNonempty : yes ≠ []) (noNonempty : no ≠ [])
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source post : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (flag : Bool) (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.ite cmp reg operand (instructionBlock yes) (instructionBlock no))
      source flag none post sectionId labelId continues breaks start)
    (x y : WordLocW 64) (chosen : Bool)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (condition : wordSemWordCmp cmp x y = some chosen) :
    ∃ final, stateRel post final ∧
      final.pc = start.pc + 2 + no.length + yes.length ∧ final.code = start.code ∧
      LabToTarget.WeightedInstructionTrace encoded
        { start with clock := start.clock + instructionBlockIfClock yes no chosen } final
        (instructionBlockIfWork encoded start.pc yes no chosen) := by
  cases chosen with
  | false =>
    have trace := flatten_instructionBlock_if_false_weighted yes no yesNonempty noNonempty cmp reg operand
      source post flag sectionId labelId continues breaks start encoded hyps x y lhs rhs condition
    simpa only [instructionBlockIfClock, instructionBlockIfWork, Bool.false_eq_true,
      ↓reduceIte, Nat.add_assoc] using trace
  | true =>
    have trace := flatten_instructionBlock_if_true_weighted yes no yesNonempty noNonempty cmp reg operand
      source post flag sectionId labelId continues breaks start encoded hyps x y lhs rhs condition
    simpa only [instructionBlockIfClock, instructionBlockIfWork, ↓reduceIte, Nat.add_assoc] using trace

/-- RISC-V execution of the actual compiled conditional prefix, preserving the
original compiler/native relations and oracle for subsequent execution. -/
theorem flatten_instructionBlock_if_native {F : Type}
    (yes no : List (HolInst 64)) (yesNonempty : yes ≠ []) (noNonempty : no ≠ [])
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source post : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (flag : Bool) (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.ite cmp reg operand (instructionBlock yes) (instructionBlock no))
      source flag none post sectionId labelId continues breaks start)
    (x y : WordLocW 64) (chosen : Bool)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (condition : wordSemWordCmp cmp x y = some chosen)
    (mc : MachineConfig 64
      Flapjack.RiscV.L3.riscv_state Flapjack.Compiler.Encoders.RiscV.Target.RiscVProjection)
    (labs : Spt (Spt Nat)) (base : BitVec 64) (asm : AsmState 64)
    (machine : Flapjack.RiscV.L3.riscv_state)
    (target : mc.target = Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget)
    (encoder : Flapjack.Compiler.Encoders.AsmProps.encoderCorrect mc.target)
    (related : Flapjack.Compiler.Backend.LabToTarget.stateRel (mc, encoded, labs, base)
      { start with clock := start.clock + instructionBlockIfClock yes no chosen } asm machine)
    (tie : Flapjack.Compiler.Backend.LabToTarget.oracleTie mc machine
      { start with clock := start.clock + instructionBlockIfClock yes no chosen }) :
    ∃ final count native finalAsm, stateRel post final ∧
      final.pc = start.pc + 2 + no.length + yes.length ∧ final.code = start.code ∧
      count ≤ instructionBlockIfWork encoded start.pc yes no chosen ∧
      (∀ clock, evaluateTargetHOL mc start.ffi
        (clock + count) machine = evaluateTargetHOL
          (Flapjack.Compiler.Backend.Semantics.TargetProps.shiftInterfer count mc) final.ffi clock native) ∧
      Flapjack.Compiler.Backend.LabToTarget.stateRel
        (Flapjack.Compiler.Backend.Semantics.TargetProps.shiftInterfer count mc, encoded, labs, base)
        final finalAsm native ∧
      Flapjack.Compiler.Backend.LabToTarget.oracleTie
        (Flapjack.Compiler.Backend.Semantics.TargetProps.shiftInterfer count mc) native final := by
  obtain ⟨final, stackRelated, pc, code, trace⟩ := flatten_instructionBlock_if_weighted
    yes no yesNonempty noNonempty cmp reg operand source post flag sectionId labelId continues breaks
    start encoded hyps x y chosen lhs rhs condition
  obtain ⟨count, native, finalAsm, bound, run, nativeRelated, finalTie⟩ :=
    LabToTarget.weightedInstructionTrace_with_oracle encoded trace mc labs base asm machine
      target encoder related tie
  exact ⟨final, count, native, finalAsm, stackRelated, pc, code, bound, run, nativeRelated, finalTie⟩

#print axioms flatten_instructionBlock_if_native
#print axioms flatten_instructionBlock_if_weighted
#print axioms flatten_instructionBlock_if_false_weighted
#print axioms flatten_instructionBlock_if_true_weighted
end InitECandidate.Runtime.StackToLab
