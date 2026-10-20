import InitECandidate.Runtime.StackFlattenShape
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

private theorem generalIf_append {α : Type} (a b : AppList α) :
    appListAppend (.append a b) = appListAppend a ++ appListAppend b :=
  (appListAppend_thm a b []).1
private theorem generalIf_list {α : Type} (xs : List α) : appListAppend (.list xs) = xs :=
  (appListAppend_thm .nil .nil xs).2.1

/-- Actual general conditional layout, with arbitrary nonempty arms. The
nonreturning flags are false; either arm may still exit on this particular run.
Instruction lengths locate bodies but are not charged as executed work. -/
theorem weighted_generalIf_layout {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNormal : (stackFlattenShape no).1 = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64) (flag : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F)
    (installed : codeInstalled start.pc (appListAppend
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag (.ite cmp reg operand yes no)
        sectionId labelId continues breaks).1) start.code) :
    let compiledYes := Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks
    let compiledNo := Flapjack.Compiler.Backend.StackToLab.flattenHOL false no sectionId compiledYes.2.2 continues breaks
    asmFetchAux start.pc start.code = some
      (.labAsm (.jumpCmp cmp reg operand (.lab sectionId compiledNo.2.2)) 0 [] 0) ∧
    codeInstalled (start.pc + 1) (appListAppend compiledNo.1) start.code ∧
    asmFetchAux (start.pc + 1 + (stackFlattenShape no).2) start.code = some
      (.labAsm (.jump (.lab sectionId (compiledNo.2.2 + 1))) 0 [] 0) ∧
    locToPc sectionId compiledNo.2.2 start.code = some (start.pc + 2 + (stackFlattenShape no).2) ∧
    codeInstalled (start.pc + 2 + (stackFlattenShape no).2) (appListAppend compiledYes.1) start.code ∧
    locToPc sectionId (compiledNo.2.2 + 1) start.code =
      some (start.pc + 2 + (stackFlattenShape no).2 + (stackFlattenShape yes).2) ∧
    ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand yes no) sectionId labelId continues breaks).1).filter
        (fun line => !isLabelHOL line)).length =
      2 + (stackFlattenShape no).2 + (stackFlattenShape yes).2 := by
  rcases hy : Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks with ⟨xs, yr, yl⟩
  rcases hn : Flapjack.Compiler.Backend.StackToLab.flattenHOL false no sectionId yl continues breaks with ⟨ys, nr, nl⟩
  have hyr : yr = false := by
    have h := (stackFlatten_noRet yes false sectionId labelId continues breaks).trans yesNormal
    simpa only [hy] using h
  have hnr : nr = false := by
    have h := (stackFlatten_noRet no false sectionId yl continues breaks).trans noNormal
    simpa only [hn] using h
  have hyl := stackFlatten_length yes false sectionId labelId continues breaks
  have hnl := stackFlatten_length no false sectionId yl continues breaks
  simp only [hy] at hyl
  simp only [hn] at hnl
  have lines : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand yes no) sectionId labelId continues breaks).1 =
      .labAsm (.jumpCmp cmp reg operand (.lab sectionId nl)) 0 [] 0 ::
        (appListAppend ys ++ (.labAsm (.jump (.lab sectionId (nl + 1))) 0 [] 0 ::
          .label sectionId nl 0 :: (appListAppend xs ++ [.label sectionId (nl + 1) 0]))) := by
    simp only [Flapjack.Compiler.Backend.StackToLab.flattenHOL, hy, hn, yesNonSkip, noNonSkip,
      hyr, hnr, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      generalIf_append, generalIf_list, List.singleton_append, List.cons_append,
      List.nil_append, List.append_assoc]
  rw [lines] at installed
  obtain ⟨fetch, rest⟩ := lineAt rfl installed
  obtain ⟨noInstalled, rest2⟩ := codeInstalledAppendImp _ _ _ _ rest
  obtain ⟨joinFetch, rest3⟩ := lineAt rfl rest2
  obtain ⟨destination, rest4⟩ := labelAt rest3
  obtain ⟨yesInstalled, rest5⟩ := codeInstalledAppendImp _ _ _ _ rest4
  obtain ⟨endLocation, _⟩ := labelAt rest5
  simp only [hnl, hyl] at joinFetch destination yesInstalled endLocation
  simp only [hy, hn]
  refine ⟨fetch, noInstalled, joinFetch, ?_, ?_, ?_, ?_⟩
  · convert destination using 1 <;> congr 1 <;> omega
  · convert yesInstalled using 1 <;> omega
  · convert endLocation using 1 <;> congr 1 <;> omega
  · rw [lines]
    simp only [isLabelHOL] at hyl hnl
    simp [List.filter_append, isLabelHOL, hyl, hnl, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] <;> omega

/-- The taken guard selects the second emitted arm; the skipped arm only
contributes its static PC offset. -/
theorem normalWeightedFlatten_generalIf_true {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNormal : (stackFlattenShape no).1 = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat)
    (bodyBound : NormalWeightedFlatten yes source price) :
    NormalWeightedFlatten (.ite cmp reg operand yes no) source
      (fun encoded pc => 3 + price encoded (pc + 2 + (stackFlattenShape no).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_generalIf_layout yes no yesNonSkip noNonSkip yesNormal noNormal
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, noInstalled, joinFetch, destination, yesInstalled, endLocation, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := updPc (start.pc + 2 + (stackFlattenShape no).2) start
  obtain ⟨final, steps, work, finalRelated, finalPc, code, bound, trace⟩ :=
    bodyBound false post sectionId labelId continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.1, yesInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some true := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_taken_update_weighted start encoded cmp reg operand _
    (start.pc + 2 + (stackFlattenShape no).2) fetch condition destination
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, 3 + work, finalRelated, ?_, code, ?_, ?_⟩
  · rw [total]
    rw [stackFlatten_length] at finalPc
    change final.pc = start.pc + 2 + (stackFlattenShape no).2 + (stackFlattenShape yes).2 at finalPc
    omega
  · change work ≤ price encoded (start.pc + 2 + (stackFlattenShape no).2) at bound
    change 3 + work ≤ 3 + price encoded (start.pc + 2 + (stackFlattenShape no).2)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The taken guard selects the second emitted arm; the skipped arm only
contributes its static PC offset. -/
theorem exitWeightedFlatten_generalIf_true {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNormal : (stackFlattenShape no).1 = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64)
    (bodyBound : ExitWeightedFlatten yes source result price) :
    ExitWeightedFlatten (.ite cmp reg operand yes no) source result
      (fun encoded pc => 3 + price encoded (pc + 2 + (stackFlattenShape no).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_generalIf_layout yes no yesNonSkip noNonSkip yesNormal noNormal
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, noInstalled, joinFetch, destination, yesInstalled, endLocation, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := updPc (start.pc + 2 + (stackFlattenShape no).2) start
  obtain ⟨final, steps, work, finalRelated, code, finalDestination, bound, trace⟩ :=
    bodyBound false post sectionId labelId continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.1, yesInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some true := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_taken_update_weighted start encoded cmp reg operand _
    (start.pc + 2 + (stackFlattenShape no).2) fetch condition destination
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, 3 + work, finalRelated, code, finalDestination, ?_, ?_⟩
  · change work ≤ price encoded (start.pc + 2 + (stackFlattenShape no).2) at bound
    change 3 + work ≤ 3 + price encoded (start.pc + 2 + (stackFlattenShape no).2)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The taken guard selects the second emitted arm; the skipped arm only
contributes its static PC offset. -/
theorem terminalWeightedFlatten_generalIf_true {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNormal : (stackFlattenShape no).1 = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyBound : TerminalWeightedFlatten yes source result outcome price) :
    TerminalWeightedFlatten (.ite cmp reg operand yes no) source result outcome
      (fun encoded pc => 3 + price encoded (pc + 2 + (stackFlattenShape no).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_generalIf_layout yes no yesNonSkip noNonSkip yesNormal noNormal
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, noInstalled, joinFetch, destination, yesInstalled, endLocation, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := updPc (start.pc + 2 + (stackFlattenShape no).2) start
  obtain ⟨final, steps, work, ffi, code, bound, trace, terminal⟩ :=
    bodyBound false post sectionId labelId continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.1, yesInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some true := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_taken_update_weighted start encoded cmp reg operand _
    (start.pc + 2 + (stackFlattenShape no).2) fetch condition destination
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, 3 + work, ffi, code, ?_, ?_, terminal⟩
  · change work ≤ price encoded (start.pc + 2 + (stackFlattenShape no).2) at bound
    change 3 + work ≤ 3 + price encoded (start.pc + 2 + (stackFlattenShape no).2)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- An early exit from the first emitted arm never executes the join jump. -/
theorem exitWeightedFlatten_generalIf_false {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNormal : (stackFlattenShape no).1 = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64)
    (bodyBound : ExitWeightedFlatten no source result price) :
    ExitWeightedFlatten (.ite cmp reg operand yes no) source result
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_generalIf_layout yes no yesNonSkip noNonSkip yesNormal noNormal
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, noInstalled, joinFetch, destination, yesInstalled, endLocation, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  obtain ⟨final, steps, work, finalRelated, code, finalDestination, bound, trace⟩ :=
    bodyBound false post sectionId
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks).2.2
      continues breaks (incPc start) encoded
      ⟨evaluated, nonerror, related, args.2, noInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some false := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_fallthrough_update_weighted start encoded cmp reg operand _ fetch condition
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, LabToTarget.controlWork 3 encoded start.pc + work,
    finalRelated, code, finalDestination, ?_, ?_⟩
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work ≤
      LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- An early exit from the first emitted arm never executes the join jump. -/
theorem terminalWeightedFlatten_generalIf_false {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNormal : (stackFlattenShape no).1 = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyBound : TerminalWeightedFlatten no source result outcome price) :
    TerminalWeightedFlatten (.ite cmp reg operand yes no) source result outcome
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_generalIf_layout yes no yesNonSkip noNonSkip yesNormal noNormal
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, noInstalled, joinFetch, destination, yesInstalled, endLocation, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  obtain ⟨final, steps, work, ffi, code, bound, trace, terminal⟩ :=
    bodyBound false post sectionId
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks).2.2
      continues breaks (incPc start) encoded
      ⟨evaluated, nonerror, related, args.2, noInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some false := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_fallthrough_update_weighted start encoded cmp reg operand _ fetch condition
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, LabToTarget.controlWork 3 encoded start.pc + work,
    ffi, code, ?_, ?_, terminal⟩
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work ≤
      LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- Normal completion of the first emitted arm reaches one join jump. Only
that jump is added to its executed price; the other body remains uncharged. -/
theorem normalWeightedFlatten_generalIf_false {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNormal : (stackFlattenShape no).1 = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (price : LabProgHOL 64 → Nat → Nat)
    (bodyBound : NormalWeightedFlatten no source price) :
    NormalWeightedFlatten (.ite cmp reg operand yes no) source
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1) + 2) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_generalIf_layout yes no yesNonSkip noNonSkip yesNormal noNormal
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, noInstalled, joinFetch, destination, yesInstalled, endLocation, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  obtain ⟨middle, steps, work, middleRelated, middlePc, middleCode, bound, child⟩ :=
    bodyBound false post sectionId
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks).2.2
      continues breaks (incPc start) encoded
      ⟨evaluated, nonerror, related, args.2, noInstalled, labels⟩
  rw [stackFlatten_length] at middlePc
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some false := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_fallthrough_update_weighted start encoded cmp reg operand _ fetch condition
  have childLift : LabToTarget.WeightedMixedTrace encoded
      {incPc start with clock := (incPc start).clock + (steps + 1)}
      {middle with clock := middle.clock + 1} work := by
    simpa only [Nat.add_assoc] using child.add_clock 1
  have prefixRun := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock (steps + 1)) childLift
  let lastLabel := (Flapjack.Compiler.Backend.StackToLab.flattenHOL false no sectionId
    (Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks).2.2
    continues breaks).2.2 + 1
  let endPc := start.pc + 2 + (stackFlattenShape no).2 + (stackFlattenShape yes).2
  have lastFetch : asmFetchAux middle.pc middle.code =
      some (.labAsm (.jump (.lab sectionId lastLabel)) 0 [] 0) := by
    rw [middlePc, middleCode]
    exact joinFetch
  have lastDestination : getPcValue (.lab sectionId lastLabel) middle = some endPc := by
    simpa only [getPcValue, middleCode, incPc, lastLabel, endPc] using endLocation
  have last := jump_update_weighted middle encoded (.lab sectionId lastLabel) endPc
    lastFetch lastDestination
  have joined := LabToTarget.weightedMixedTrace_append prefixRun last.toMixed
  refine ⟨updPc endPc middle, 1 + steps + 1,
    LabToTarget.controlWork 3 encoded start.pc + work + 2,
    middleRelated, ?_, middleCode, ?_, ?_⟩
  · rw [total]
    change endPc = start.pc + (2 + (stackFlattenShape no).2 + (stackFlattenShape yes).2)
    dsimp only [endPc]
    omega
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work + 2 ≤
      LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1) + 2
    omega
  · simpa only [Nat.add_assoc] using joined

#print axioms normalWeightedFlatten_generalIf_false
#print axioms normalWeightedFlatten_generalIf_true
#print axioms exitWeightedFlatten_generalIf_true
#print axioms terminalWeightedFlatten_generalIf_true
#print axioms exitWeightedFlatten_generalIf_false
#print axioms terminalWeightedFlatten_generalIf_false
#print axioms weighted_generalIf_layout
end InitECandidate.Runtime.StackToLab
