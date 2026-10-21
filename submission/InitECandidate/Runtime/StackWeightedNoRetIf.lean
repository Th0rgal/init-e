import InitECandidate.Runtime.StackWeightedGeneralIf
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

private theorem noRetIf_append {α : Type} (a b : AppList α) :
    appListAppend (.append a b) = appListAppend a ++ appListAppend b :=
  (appListAppend_thm a b []).1
private theorem noRetIf_list {α : Type} (xs : List α) : appListAppend (.list xs) = xs :=
  (appListAppend_thm .nil .nil xs).2.1

/-- The compiler places the statically nonreturning yes arm first,
omitting a join jump. The other arm determines only a static layout offset. -/
theorem weighted_yesNoRetIf_layout {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNoReturn : (stackFlattenShape yes).1 = true)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64) (flag : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F)
    (installed : codeInstalled start.pc (appListAppend
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag (.ite cmp reg operand yes no)
        sectionId labelId continues breaks).1) start.code) :
    let compiledYes := Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks
    let compiledNo := Flapjack.Compiler.Backend.StackToLab.flattenHOL false no sectionId compiledYes.2.2 continues breaks
    asmFetchAux start.pc start.code = some
      (.labAsm (.jumpCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand (.lab sectionId compiledNo.2.2)) 0 [] 0) ∧
    codeInstalled (start.pc + 1) (appListAppend compiledYes.1) start.code ∧
    locToPc sectionId compiledNo.2.2 start.code = some (start.pc + 1 + (stackFlattenShape yes).2) ∧
    codeInstalled (start.pc + 1 + (stackFlattenShape yes).2) (appListAppend compiledNo.1) start.code ∧
    ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand yes no) sectionId labelId continues breaks).1).filter
        (fun line => !isLabelHOL line)).length =
      1 + (stackFlattenShape yes).2 + (stackFlattenShape no).2 := by
  rcases hy : Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks with ⟨xs, yr, yl⟩
  rcases hn : Flapjack.Compiler.Backend.StackToLab.flattenHOL false no sectionId yl continues breaks with ⟨ys, nr, nl⟩
  have hyr : yr = true := by
    have h := (stackFlatten_noRet yes false sectionId labelId continues breaks).trans yesNoReturn
    simpa only [hy] using h
  have hyl := stackFlatten_length yes false sectionId labelId continues breaks
  have hnl := stackFlatten_length no false sectionId yl continues breaks
  simp only [hy] at hyl
  simp only [hn] at hnl
  have lines : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand yes no) sectionId labelId continues breaks).1 =
      .labAsm (.jumpCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand (.lab sectionId nl)) 0 [] 0 ::
        (appListAppend xs ++ (.label sectionId nl 0 :: appListAppend ys)) := by
    simp only [Flapjack.Compiler.Backend.StackToLab.flattenHOL, hy, hn, yesNonSkip, noNonSkip,
      hyr, Bool.false_and, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      noRetIf_append, noRetIf_list, List.singleton_append, List.cons_append,
      List.nil_append, List.append_assoc]
  rw [lines] at installed
  obtain ⟨fetch, rest⟩ := lineAt rfl installed
  obtain ⟨firstInstalled, rest2⟩ := codeInstalledAppendImp _ _ _ _ rest
  obtain ⟨destination, secondInstalled⟩ := labelAt rest2
  simp only [hnl, hyl] at destination secondInstalled
  simp only [hy, hn]
  refine ⟨fetch, firstInstalled, destination, secondInstalled, ?_⟩
  rw [lines]
  simp only [isLabelHOL] at hyl hnl
  simp [List.filter_append, isLabelHOL, hyl, hnl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The selected yes arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem exitWeightedFlatten_yesNoRetIf_true {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNoReturn : (stackFlattenShape yes).1 = true)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64)
    (bodyBound : ExitWeightedFlatten yes source result price) :
    ExitWeightedFlatten (.ite cmp reg operand yes no) source result
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_yesNoRetIf_layout yes no yesNonSkip noNonSkip yesNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := incPc start
  obtain ⟨final, steps, work, finalRelated, code, finalDestination, bound, trace⟩ :=
    bodyBound false post sectionId labelId continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.1, firstInstalled, labels⟩
  have condition : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) (start.regs reg) (regImm operand start) = some false := by
    rw [Prelude.wordCmpNegate, InstCorrect.regOfLookup related lhs,
      StateRel.stateRelGetVarImm ⟨related, rhs⟩, chosen]
    rfl
  have branch := branch_fallthrough_update_weighted start encoded (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand _ fetch condition
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, LabToTarget.controlWork 3 encoded start.pc + work, finalRelated, code, finalDestination, ?_, ?_⟩
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work ≤ LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected yes arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem terminalWeightedFlatten_yesNoRetIf_true {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNoReturn : (stackFlattenShape yes).1 = true)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyBound : TerminalWeightedFlatten yes source result outcome price) :
    TerminalWeightedFlatten (.ite cmp reg operand yes no) source result outcome
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_yesNoRetIf_layout yes no yesNonSkip noNonSkip yesNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := incPc start
  obtain ⟨final, steps, work, ffi, code, bound, trace, terminal⟩ :=
    bodyBound false post sectionId labelId continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.1, firstInstalled, labels⟩
  have condition : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) (start.regs reg) (regImm operand start) = some false := by
    rw [Prelude.wordCmpNegate, InstCorrect.regOfLookup related lhs,
      StateRel.stateRelGetVarImm ⟨related, rhs⟩, chosen]
    rfl
  have branch := branch_fallthrough_update_weighted start encoded (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand _ fetch condition
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, LabToTarget.controlWork 3 encoded start.pc + work, ffi, code, ?_, ?_, terminal⟩
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work ≤ LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected no arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem normalWeightedFlatten_yesNoRetIf_false {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNoReturn : (stackFlattenShape yes).1 = true)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (price : LabProgHOL 64 → Nat → Nat)
    (bodyBound : NormalWeightedFlatten no source price) :
    NormalWeightedFlatten (.ite cmp reg operand yes no) source
      (fun encoded pc => 3 + price encoded (pc + 1 + (stackFlattenShape yes).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_yesNoRetIf_layout yes no yesNonSkip noNonSkip yesNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := updPc (start.pc + 1 + (stackFlattenShape yes).2) start
  obtain ⟨final, steps, work, finalRelated, finalPc, code, bound, trace⟩ :=
    bodyBound false post sectionId (Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks).2.2 continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.2, secondInstalled, labels⟩
  have condition : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) (start.regs reg) (regImm operand start) = some true := by
    rw [Prelude.wordCmpNegate, InstCorrect.regOfLookup related lhs,
      StateRel.stateRelGetVarImm ⟨related, rhs⟩, chosen]
    rfl
  have branch := branch_taken_update_weighted start encoded (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand _
    (start.pc + 1 + (stackFlattenShape yes).2) fetch condition destination
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, 3 + work, finalRelated, ?_, code, ?_, ?_⟩
  · rw [total]
    rw [stackFlatten_length] at finalPc
    change final.pc = start.pc + 1 + (stackFlattenShape yes).2 + (stackFlattenShape no).2 at finalPc
    omega
  · change work ≤ price encoded (start.pc + 1 + (stackFlattenShape yes).2) at bound
    change 3 + work ≤ 3 + price encoded (start.pc + 1 + (stackFlattenShape yes).2)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected no arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem exitWeightedFlatten_yesNoRetIf_false {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNoReturn : (stackFlattenShape yes).1 = true)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64)
    (bodyBound : ExitWeightedFlatten no source result price) :
    ExitWeightedFlatten (.ite cmp reg operand yes no) source result
      (fun encoded pc => 3 + price encoded (pc + 1 + (stackFlattenShape yes).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_yesNoRetIf_layout yes no yesNonSkip noNonSkip yesNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := updPc (start.pc + 1 + (stackFlattenShape yes).2) start
  obtain ⟨final, steps, work, finalRelated, code, finalDestination, bound, trace⟩ :=
    bodyBound false post sectionId (Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks).2.2 continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.2, secondInstalled, labels⟩
  have condition : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) (start.regs reg) (regImm operand start) = some true := by
    rw [Prelude.wordCmpNegate, InstCorrect.regOfLookup related lhs,
      StateRel.stateRelGetVarImm ⟨related, rhs⟩, chosen]
    rfl
  have branch := branch_taken_update_weighted start encoded (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand _
    (start.pc + 1 + (stackFlattenShape yes).2) fetch condition destination
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, 3 + work, finalRelated, code, finalDestination, ?_, ?_⟩
  · change work ≤ price encoded (start.pc + 1 + (stackFlattenShape yes).2) at bound
    change 3 + work ≤ 3 + price encoded (start.pc + 1 + (stackFlattenShape yes).2)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected no arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem terminalWeightedFlatten_yesNoRetIf_false {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNoReturn : (stackFlattenShape yes).1 = true)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyBound : TerminalWeightedFlatten no source result outcome price) :
    TerminalWeightedFlatten (.ite cmp reg operand yes no) source result outcome
      (fun encoded pc => 3 + price encoded (pc + 1 + (stackFlattenShape yes).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_yesNoRetIf_layout yes no yesNonSkip noNonSkip yesNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := updPc (start.pc + 1 + (stackFlattenShape yes).2) start
  obtain ⟨final, steps, work, ffi, code, bound, trace, terminal⟩ :=
    bodyBound false post sectionId (Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks).2.2 continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.2, secondInstalled, labels⟩
  have condition : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) (start.regs reg) (regImm operand start) = some true := by
    rw [Prelude.wordCmpNegate, InstCorrect.regOfLookup related lhs,
      StateRel.stateRelGetVarImm ⟨related, rhs⟩, chosen]
    rfl
  have branch := branch_taken_update_weighted start encoded (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand _
    (start.pc + 1 + (stackFlattenShape yes).2) fetch condition destination
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, 3 + work, ffi, code, ?_, ?_, terminal⟩
  · change work ≤ price encoded (start.pc + 1 + (stackFlattenShape yes).2) at bound
    change 3 + work ≤ 3 + price encoded (start.pc + 1 + (stackFlattenShape yes).2)
    omega
  · simpa only [Nat.add_assoc] using joined

#print axioms weighted_yesNoRetIf_layout
#print axioms exitWeightedFlatten_yesNoRetIf_true
#print axioms terminalWeightedFlatten_yesNoRetIf_true
#print axioms normalWeightedFlatten_yesNoRetIf_false
#print axioms exitWeightedFlatten_yesNoRetIf_false
#print axioms terminalWeightedFlatten_yesNoRetIf_false
/-- The compiler places the statically nonreturning no arm first,
omitting a join jump. The other arm determines only a static layout offset. -/
theorem weighted_noNoRetIf_layout {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNoReturn : (stackFlattenShape no).1 = true)
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
    locToPc sectionId compiledNo.2.2 start.code = some (start.pc + 1 + (stackFlattenShape no).2) ∧
    codeInstalled (start.pc + 1 + (stackFlattenShape no).2) (appListAppend compiledYes.1) start.code ∧
    ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand yes no) sectionId labelId continues breaks).1).filter
        (fun line => !isLabelHOL line)).length =
      1 + (stackFlattenShape no).2 + (stackFlattenShape yes).2 := by
  rcases hy : Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks with ⟨xs, yr, yl⟩
  rcases hn : Flapjack.Compiler.Backend.StackToLab.flattenHOL false no sectionId yl continues breaks with ⟨ys, nr, nl⟩
  have hyr : yr = false := by
    have h := (stackFlatten_noRet yes false sectionId labelId continues breaks).trans yesNormal
    simpa only [hy] using h
  have hnr : nr = true := by
    have h := (stackFlatten_noRet no false sectionId yl continues breaks).trans noNoReturn
    simpa only [hn] using h
  have hyl := stackFlatten_length yes false sectionId labelId continues breaks
  have hnl := stackFlatten_length no false sectionId yl continues breaks
  simp only [hy] at hyl
  simp only [hn] at hnl
  have lines : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand yes no) sectionId labelId continues breaks).1 =
      .labAsm (.jumpCmp cmp reg operand (.lab sectionId nl)) 0 [] 0 ::
        (appListAppend ys ++ (.label sectionId nl 0 :: appListAppend xs)) := by
    simp only [Flapjack.Compiler.Backend.StackToLab.flattenHOL, hy, hn, yesNonSkip, noNonSkip,
      hyr, hnr, Bool.false_and, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      noRetIf_append, noRetIf_list, List.singleton_append, List.cons_append,
      List.nil_append, List.append_assoc]
  rw [lines] at installed
  obtain ⟨fetch, rest⟩ := lineAt rfl installed
  obtain ⟨firstInstalled, rest2⟩ := codeInstalledAppendImp _ _ _ _ rest
  obtain ⟨destination, secondInstalled⟩ := labelAt rest2
  simp only [hnl, hyl] at destination secondInstalled
  simp only [hy, hn]
  refine ⟨fetch, firstInstalled, destination, secondInstalled, ?_⟩
  rw [lines]
  simp only [isLabelHOL] at hyl hnl
  simp [List.filter_append, isLabelHOL, hyl, hnl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The selected no arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem exitWeightedFlatten_noNoRetIf_false {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNoReturn : (stackFlattenShape no).1 = true)
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
  have layout := weighted_noNoRetIf_layout yes no yesNonSkip noNonSkip yesNormal noNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := incPc start
  obtain ⟨final, steps, work, finalRelated, code, finalDestination, bound, trace⟩ :=
    bodyBound false post sectionId (Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks).2.2 continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.2, firstInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some false := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_fallthrough_update_weighted start encoded cmp reg operand _ fetch condition
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, LabToTarget.controlWork 3 encoded start.pc + work, finalRelated, code, finalDestination, ?_, ?_⟩
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work ≤ LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected no arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem terminalWeightedFlatten_noNoRetIf_false {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNoReturn : (stackFlattenShape no).1 = true)
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
  have layout := weighted_noNoRetIf_layout yes no yesNonSkip noNonSkip yesNormal noNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := incPc start
  obtain ⟨final, steps, work, ffi, code, bound, trace, terminal⟩ :=
    bodyBound false post sectionId (Flapjack.Compiler.Backend.StackToLab.flattenHOL false yes sectionId labelId continues breaks).2.2 continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.2, firstInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some false := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_fallthrough_update_weighted start encoded cmp reg operand _ fetch condition
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, LabToTarget.controlWork 3 encoded start.pc + work, ffi, code, ?_, ?_, terminal⟩
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work ≤ LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected yes arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem normalWeightedFlatten_noNoRetIf_true {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNoReturn : (stackFlattenShape no).1 = true)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat)
    (bodyBound : NormalWeightedFlatten yes source price) :
    NormalWeightedFlatten (.ite cmp reg operand yes no) source
      (fun encoded pc => 3 + price encoded (pc + 1 + (stackFlattenShape no).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_noNoRetIf_layout yes no yesNonSkip noNonSkip yesNormal noNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := updPc (start.pc + 1 + (stackFlattenShape no).2) start
  obtain ⟨final, steps, work, finalRelated, finalPc, code, bound, trace⟩ :=
    bodyBound false post sectionId labelId continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.1, secondInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some true := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_taken_update_weighted start encoded cmp reg operand _
    (start.pc + 1 + (stackFlattenShape no).2) fetch condition destination
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, 3 + work, finalRelated, ?_, code, ?_, ?_⟩
  · rw [total]
    rw [stackFlatten_length] at finalPc
    change final.pc = start.pc + 1 + (stackFlattenShape no).2 + (stackFlattenShape yes).2 at finalPc
    omega
  · change work ≤ price encoded (start.pc + 1 + (stackFlattenShape no).2) at bound
    change 3 + work ≤ 3 + price encoded (start.pc + 1 + (stackFlattenShape no).2)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected yes arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem exitWeightedFlatten_noNoRetIf_true {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNoReturn : (stackFlattenShape no).1 = true)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64)
    (bodyBound : ExitWeightedFlatten yes source result price) :
    ExitWeightedFlatten (.ite cmp reg operand yes no) source result
      (fun encoded pc => 3 + price encoded (pc + 1 + (stackFlattenShape no).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_noNoRetIf_layout yes no yesNonSkip noNonSkip yesNormal noNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := updPc (start.pc + 1 + (stackFlattenShape no).2) start
  obtain ⟨final, steps, work, finalRelated, code, finalDestination, bound, trace⟩ :=
    bodyBound false post sectionId labelId continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.1, secondInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some true := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_taken_update_weighted start encoded cmp reg operand _
    (start.pc + 1 + (stackFlattenShape no).2) fetch condition destination
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, 3 + work, finalRelated, code, finalDestination, ?_, ?_⟩
  · change work ≤ price encoded (start.pc + 1 + (stackFlattenShape no).2) at bound
    change 3 + work ≤ 3 + price encoded (start.pc + 1 + (stackFlattenShape no).2)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected yes arm supplies its actual trace; the other arm is
uncharged, and this layout has no join jump. -/
theorem terminalWeightedFlatten_noNoRetIf_true {F : Type}
    (yes no : HolProg 64)
    (yesNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip yes = false)
    (noNonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip no = false)
    (yesNormal : (stackFlattenShape yes).1 = false)
    (noNoReturn : (stackFlattenShape no).1 = true)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat) (result : StackSemResult 64) (outcome : HolOutcome)
    (bodyBound : TerminalWeightedFlatten yes source result outcome price) :
    TerminalWeightedFlatten (.ite cmp reg operand yes no) source result outcome
      (fun encoded pc => 3 + price encoded (pc + 1 + (stackFlattenShape no).2)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_noNoRetIf_layout yes no yesNonSkip noNonSkip yesNormal noNoReturn
    cmp reg operand flag sectionId labelId continues breaks start installed
  dsimp only at layout
  obtain ⟨fetch, firstInstalled, destination, secondInstalled, total⟩ := layout
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  let childStart := updPc (start.pc + 1 + (stackFlattenShape no).2) start
  obtain ⟨final, steps, work, ffi, code, bound, trace, terminal⟩ :=
    bodyBound false post sectionId labelId continues breaks childStart encoded
      ⟨evaluated, nonerror, related, args.1, secondInstalled, labels⟩
  have condition : wordSemWordCmp cmp (start.regs reg) (regImm operand start) = some true := by
    rw [InstCorrect.regOfLookup related lhs, StateRel.stateRelGetVarImm ⟨related, rhs⟩]
    exact chosen
  have branch := branch_taken_update_weighted start encoded cmp reg operand _
    (start.pc + 1 + (stackFlattenShape no).2) fetch condition destination
  have joined := LabToTarget.weightedMixedTrace_append (branch.toMixed.add_clock steps) trace
  refine ⟨final, 1 + steps, 3 + work, ffi, code, ?_, ?_, terminal⟩
  · change work ≤ price encoded (start.pc + 1 + (stackFlattenShape no).2) at bound
    change 3 + work ≤ 3 + price encoded (start.pc + 1 + (stackFlattenShape no).2)
    omega
  · simpa only [Nat.add_assoc] using joined

#print axioms weighted_noNoRetIf_layout
#print axioms exitWeightedFlatten_noNoRetIf_false
#print axioms terminalWeightedFlatten_noNoRetIf_false
#print axioms normalWeightedFlatten_noNoRetIf_true
#print axioms exitWeightedFlatten_noNoRetIf_true
#print axioms terminalWeightedFlatten_noNoRetIf_true
end InitECandidate.Runtime.StackToLab
