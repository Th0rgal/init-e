import InitECandidate.Runtime.StackWeightedTerminal
import InitECandidate.Runtime.StackWeightedExit
import InitECandidate.Runtime.StackWeightedBranch
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

private theorem skipIf_appAppend {α : Type} (a b : AppList α) :
    appListAppend (.append a b) = appListAppend a ++ appListAppend b :=
  (appListAppend_thm a b []).1
private theorem skipIf_appList {α : Type} (lines : List α) :
    appListAppend (.list lines) = lines := (appListAppend_thm .nil .nil lines).2.1

def skipIfBodyLength (body : HolProg 64) (sectionId labelId : Nat)
    (continues breaks : List Nat) : Nat :=
  ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL false body sectionId labelId continues breaks).1).filter
    (fun line => !isLabelHOL line)).length

/-- The literal one-empty-arm compiler layout. The active body is at PC+1 and
the opposite condition jumps to its end; labels add no instruction cost. -/
theorem weighted_skipIf_layout {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64) (flag : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F)
    (installed : codeInstalled start.pc (appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand body .skip) sectionId labelId continues breaks).1) start.code) :
    let compiled := Flapjack.Compiler.Backend.StackToLab.flattenHOL false body sectionId labelId continues breaks
    asmFetchAux start.pc start.code = some
      (.labAsm (.jumpCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand (.lab sectionId compiled.2.2)) 0 [] 0) ∧
    codeInstalled (start.pc + 1) (appListAppend compiled.1) start.code ∧
    locToPc sectionId compiled.2.2 start.code =
      some (start.pc + 1 + skipIfBodyLength body sectionId labelId continues breaks) ∧
    ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand body .skip) sectionId labelId continues breaks).1).filter
        (fun line => !isLabelHOL line)).length =
      1 + skipIfBodyLength body sectionId labelId continues breaks := by
  rcases hb : Flapjack.Compiler.Backend.StackToLab.flattenHOL false body sectionId labelId continues breaks with ⟨xs, nr, next⟩
  have lines : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.ite cmp reg operand body .skip) sectionId labelId continues breaks).1 =
      .labAsm (.jumpCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg operand (.lab sectionId next)) 0 [] 0 ::
        (appListAppend xs ++ [.label sectionId next 0]) := by
    simp only [Flapjack.Compiler.Backend.StackToLab.flattenHOL, hb, nonSkip,
      show Flapjack.Compiler.Backend.StackToLab.stackIsSkip (.skip : HolProg 64) = true from rfl,
      Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, skipIf_appAppend, skipIf_appList, List.singleton_append, List.cons_append, List.nil_append]
  rw [lines] at installed
  obtain ⟨fetch, rest⟩ := lineAt rfl installed
  obtain ⟨bodyInstalled, endInstalled⟩ := codeInstalledAppendImp _ _ _ _ rest
  obtain ⟨destination, _⟩ := labelAt endInstalled
  simp only [hb]
  refine ⟨fetch, bodyInstalled, ?_, ?_⟩
  · simpa only [skipIfBodyLength, hb] using destination
  · rw [lines]
    simp [List.filter_append, isLabelHOL, skipIfBodyLength, hb, Nat.add_comm]

/-- A selected nonempty arm with an empty else branch, for normal completion.
The actual false negated branch falls through to the selected body's prefix. -/
theorem normalWeightedFlatten_skipIf_true {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat) (bodyBound : NormalWeightedFlatten body source price) :
    NormalWeightedFlatten (.ite cmp reg operand body .skip) source
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_skipIf_layout body nonSkip cmp reg operand flag sectionId labelId continues breaks start installed
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  obtain ⟨final, steps, work, finalRelated, finalPc, code, bound, trace⟩ :=
    bodyBound false post sectionId labelId continues breaks (incPc start) encoded
      ⟨evaluated, nonerror, related, args.1, layout.2.1, labels⟩
  have cmpFalse : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp)
      (start.regs reg) (regImm operand start) = some false := by
    rw [Prelude.wordCmpNegate, InstCorrect.regOfLookup related lhs,
      StateRel.stateRelGetVarImm ⟨related, rhs⟩, chosen]
    rfl
  have branch := branch_fallthrough_update_weighted start encoded _ reg operand _ layout.1 cmpFalse
  have joined := LabToTarget.weightedInstructionTrace_append (branch.add_clock steps) trace
  refine ⟨final, 1 + steps, LabToTarget.controlWork 3 encoded start.pc + work,
    finalRelated, ?_, code, ?_, ?_⟩
  · rw [layout.2.2.2]
    change final.pc = start.pc + (1 + skipIfBodyLength body sectionId labelId continues breaks)
    change final.pc = start.pc + 1 + skipIfBodyLength body sectionId labelId continues breaks at finalPc
    omega
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work ≤
      LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected arm may instead leave via its actual control destination. -/
theorem exitWeightedFlatten_skipIf_true {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat) (exit : StackSemResult 64)
    (bodyBound : ExitWeightedFlatten body source exit price) :
    ExitWeightedFlatten (.ite cmp reg operand body .skip) source exit
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_skipIf_layout body nonSkip cmp reg operand flag sectionId labelId continues breaks start installed
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  obtain ⟨final, steps, work, finalRelated, code, destination, bound, trace⟩ :=
    bodyBound false post sectionId labelId continues breaks (incPc start) encoded
      ⟨evaluated, nonerror, related, args.1, layout.2.1, labels⟩
  have cmpFalse : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp)
      (start.regs reg) (regImm operand start) = some false := by
    rw [Prelude.wordCmpNegate, InstCorrect.regOfLookup related lhs,
      StateRel.stateRelGetVarImm ⟨related, rhs⟩, chosen]
    rfl
  have branch := branch_fallthrough_update_weighted start encoded _ reg operand _ layout.1 cmpFalse
  have joined := LabToTarget.weightedInstructionTrace_append (branch.add_clock steps) trace
  refine ⟨final, 1 + steps, LabToTarget.controlWork 3 encoded start.pc + work,
    finalRelated, code, destination, ?_, ?_⟩
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work ≤
      LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- The selected arm may terminate; the terminal witness is retained unchanged. -/
theorem terminalWeightedFlatten_skipIf_true {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some true)
    (price : LabProgHOL 64 → Nat → Nat) (exit : StackSemResult 64) (outcome : HolOutcome)
    (bodyBound : TerminalWeightedFlatten body source exit outcome price) :
    TerminalWeightedFlatten (.ite cmp reg operand body .skip) source exit outcome
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc + price encoded (pc + 1)) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen] at evaluated
  have layout := weighted_skipIf_layout body nonSkip cmp reg operand flag sectionId labelId continues breaks start installed
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  obtain ⟨final, steps, work, ffi, code, bound, trace, terminal⟩ :=
    bodyBound false post sectionId labelId continues breaks (incPc start) encoded
      ⟨evaluated, nonerror, related, args.1, layout.2.1, labels⟩
  have cmpFalse : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp)
      (start.regs reg) (regImm operand start) = some false := by
    rw [Prelude.wordCmpNegate, InstCorrect.regOfLookup related lhs,
      StateRel.stateRelGetVarImm ⟨related, rhs⟩, chosen]
    rfl
  have branch := branch_fallthrough_update_weighted start encoded _ reg operand _ layout.1 cmpFalse
  have joined := LabToTarget.weightedInstructionTrace_append (branch.add_clock steps) trace
  refine ⟨final, 1 + steps, LabToTarget.controlWork 3 encoded start.pc + work,
    ffi, code, ?_, ?_, terminal⟩
  · change work ≤ price encoded (start.pc + 1) at bound
    change LabToTarget.controlWork 3 encoded start.pc + work ≤
      LabToTarget.controlWork 3 encoded start.pc + price encoded (start.pc + 1)
    omega
  · simpa only [Nat.add_assoc] using joined

/-- Choosing the empty else arm jumps over the body and charges only the
actual taken branch, independent of the unexecuted body's size or work. -/
theorem normalWeightedFlatten_skipIf_false {F : Type}
    (body : HolProg 64) (nonSkip : Flapjack.Compiler.Backend.StackToLab.stackIsSkip body = false)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some false) :
    NormalWeightedFlatten (.ite cmp reg operand body .skip) source (fun _ _ => 3) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, _, related, _, installed, _⟩
  rw [StackSemEvaluate.evaluate_ite, lhs, rhs] at evaluated
  simp only [chosen, StackSemEvaluate.evaluate_skip, Prod.mk.injEq, true_and] at evaluated
  subst post
  have layout := weighted_skipIf_layout body nonSkip cmp reg operand flag sectionId labelId continues breaks start installed
  have condition : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp)
      (start.regs reg) (regImm operand start) = some true := by
    rw [Prelude.wordCmpNegate, InstCorrect.regOfLookup related lhs,
      StateRel.stateRelGetVarImm ⟨related, rhs⟩, chosen]
    rfl
  let targetPc := start.pc + 1 + skipIfBodyLength body sectionId labelId continues breaks
  have trace := branch_taken_update_weighted start encoded _ reg operand _ targetPc
    layout.1 condition layout.2.2.1
  refine ⟨updPc targetPc start, 1, 3, related, ?_, rfl, Nat.le_refl _, trace⟩
  rw [layout.2.2.2]
  simp only [updPc, targetPc]
  omega

#print axioms normalWeightedFlatten_skipIf_false
#print axioms exitWeightedFlatten_skipIf_true
#print axioms terminalWeightedFlatten_skipIf_true
#print axioms weighted_skipIf_layout
#print axioms normalWeightedFlatten_skipIf_true
end InitECandidate.Runtime.StackToLab
