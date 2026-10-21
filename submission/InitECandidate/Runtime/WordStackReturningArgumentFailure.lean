import InitECandidate.Runtime.WordStackReturningStoppedPrelude
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning.Execution
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Original compiler premises derive a stopped argument prelude and its
executed cost; no target execution or desired runtime bound is assumed. -/
theorem compiledCall_insufficient_args_cost {F : Type}
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
    (insufficient : target.stackSpace <
      Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (frameSmall : f ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92) :
    stackExecutionCost (fun p _ => price p) compiled target ≤
      26 + 39 * Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
  obtain ⟨saved, preludeRun, pushedRelation, savedRelation, _, savedSpace⟩ :=
    evaluatePrelude ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs bs savedBitmaps finalBitmaps n savedIndex finalIndex
      destinationCode savedCode returnCode destination guards related conventions maximum
      destinationCompile savedCompile returnCompile lengthBound bitmapBound bitmapPrefix
  have useStack : saved.useStack = true := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have argumentRun := evaluateStackArgumentsInsufficient k f frame destination (args.length+1)
    saved useStack (by rwa [savedSpace])
  obtain ⟨get, bad, _, _, _⟩ := guards
  obtain ⟨destinationTarget, destinationRun, _, _, _, _⟩ :=
    CallDest.callDestLemma ac k f frame dest args source target lens destinationCode
      destination xs (some (values,names,retCode,l1,l2))
      ⟨bad,related,destinationCompile,get⟩
  have savedRun := preludeRun 0
  simp only [Nat.add_zero] at savedRun
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun] at savedRun
  simp only at savedRun
  have stoppedPrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (stackArgsNative destination (args.length+1) (k,f,frame))), target) =
      (some (.halt (.word (BitVec.ofNat 64 2))), StackSemStateOps.emptyEnv saved) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    exact argumentRun
  exact compiledCall_cost_stopped_prelude ac k f frame values names retCode l1 l2 dest args
    bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled
    destination target (StackSemStateOps.emptyEnv saved) (.halt (.word (BitVec.ofNat 64 2)))
    destinationCompile savedCompile returnCompile compilation frameSmall argsSmall stoppedPrelude

#print axioms compiledCall_insufficient_args_cost
end InitECandidate.Runtime.WordToStack.ExecutedReturning
