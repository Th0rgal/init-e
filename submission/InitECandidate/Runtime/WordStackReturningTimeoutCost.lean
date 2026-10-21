import InitECandidate.Runtime.WordStackReturningPreludeCost
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning.Execution
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- A zero-clock returning call pays setup and its call node, without
executing or pricing a callee or continuation. The prelude state is derived. -/
theorem compiledCall_timeout_cost {F : Type}
    (ac : AsmConfigExact 64) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (result : Option (WordSemResult 64))
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (bs savedBitmaps finalBitmaps : AppList (BitVec 64))
    (n savedIndex finalIndex : Nat) (destinationCode savedCode returnCode : HolProg 64)
    (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (compiled : HolProg 64)
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, f, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace)
    (zero : source.clock = 0)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (frameSmall : f ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92) :
    stackExecutionCost (fun p _ => price p) compiled target ≤
      38 + 39 * Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps, savedIndex)
    (k, f, frame) returnCode (finalBitmaps, finalIndex) returnCompile).trans bitmapPrefix
  obtain ⟨destinationTarget, saved, moved, _, _, _, _, _, _, destinationRun, savedRun,
    moveRun, savedRelation, _, _, _, _, _, _, found, _, stack, regs, movedState⟩ :=
    prepareCalleeDestination ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile lengthBound bitmapBound
      savedPrefix space
  have movedClock : moved.clock = 0 := by
    rw [movedState]
    exact savedRelation.1.symm.trans zero
  have completePrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (stackArgsNative destination (args.length+1) (k,f,frame))), target) =
      (none,moved) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    exact moveRun
  have callCost : stackExecutionCost (fun p _ => price p)
      (.call (some (.seq .skip (copyRetNative false false (k,f,frame) values returnCode),0,l1,l2)) destination none)
      {moved with clock := moved.clock + 0} ≤ 12 := by
    rw [stackExecutionCost]
    simp only [Nat.add_zero, movedClock, ↓reduceIte]
    exact (caps.le _).trans (by cases destination <;> simp [removalLocalPrice, nativePriceWithGap, callJumpWork])
  have bound := compiledCall_cost_from_prelude (price := price) ac k f frame values names retCode l1 l2 dest args
    bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled
    destination target moved 0 12 destinationCompile savedCompile returnCompile compilation
    frameSmall argsSmall completePrelude callCost
  simp only [Nat.add_zero] at bound
  change stackExecutionCost (fun p _ => price p) compiled target ≤ _ at bound
  omega

#print axioms compiledCall_timeout_cost
end InitECandidate.Runtime.WordToStack.ExecutedReturning
