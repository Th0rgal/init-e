import InitECandidate.Runtime.StackWeightedExit
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
  have tf : Flapjack.Compiler.Backend.StackToLab.flattenHOL flag (.loop body)
      sectionId labelId continues breaks =
      Flapjack.Compiler.Backend.StackToLab.flattenHOL false (.loop body) sectionId labelId continues breaks := by
    cases flag
    · rfl
    · exact flattenTF (by simp [Flapjack.Compiler.Backend.StackToLab.isSeqHOL])
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false body sectionId
      (labelId + 2) (labelId :: continues) ((labelId + 1) :: breaks) with ⟨xs, nr, next⟩
  have flat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.loop body) sectionId labelId continues breaks).1 =
      .label sectionId labelId 0 :: (appListAppend xs ++
        [.labAsm (.jump (.lab sectionId labelId)) 0 [] 0, .label sectionId (labelId + 1) 0]) := by
    rw [tf, Flapjack.Compiler.Backend.StackToLab.flattenHOL]
    simp [h1, appListAppendAppend, appListAppendList]
  have total : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.loop body) sectionId labelId continues breaks).1).filter
        (fun line => !isLabelHOL line)).length =
      ((appListAppend xs).filter (fun line => !isLabelHOL line)).length + 1 := by
    rw [flat]; simp [List.filter_append, isLabelHOL]
  rw [flat] at installed
  obtain ⟨locEntry, inst1⟩ := labelAt installed
  obtain ⟨instBody, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst1
  obtain ⟨_, instExit⟩ := lineAt rfl instRest
  obtain ⟨locExit, _⟩ := labelAt instExit
  have labelsBody : ∀ k ∈ (labelId :: continues) ++ ((labelId + 1) :: breaks) ++ [0],
      (locToPc sectionId k start.code).isSome := by
    intro k member
    by_cases first : k = labelId
    · subst first; simp [locEntry]
    by_cases last : k = labelId + 1
    · subst last; simp [locExit]
    apply labels k
    simp only [List.cons_append, List.mem_cons, List.mem_append] at member ⊢
    tauto
  obtain ⟨final, steps, work, finalRelated, code, destination, bound, trace⟩ :=
    bodyBound false middle sectionId (labelId + 2) (labelId :: continues)
      ((labelId + 1) :: breaks) start encoded
      ⟨run, by simp, related, args, by rw [h1]; exact instBody, labelsBody⟩
  have finalPc : final.pc = start.pc +
      ((appListAppend xs).filter (fun line => !isLabelHOL line)).length + 1 := by
    simp only [WeightedExitDestination, resultView,
      Flapjack.Compiler.Backend.StackToLab.findLabHOL, List.getElem?_cons_zero,
      Option.getD_some, code] at destination
    have equal := Option.some.inj (locExit.symm.trans destination)
    omega
  exact ⟨final, steps, work, finalRelated, by rw [total]; omega, code, bound, trace⟩

#print axioms normalWeightedFlatten_loop_break
end InitECandidate.Runtime.StackToLab
