import InitECandidate.Runtime.WordStackHandlerPreludeCost
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler.Execution
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]


/-- A zero-clock handler call pays only its executed setup and call node. -/
theorem compiledHandlerCall_timeout_cost {F : Type}
    (ac : AsmConfigExact 64) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec 64))
    (source sourcePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (result : Option (WordSemResult 64))
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (bs savedBitmaps finalBitmaps : AppList (BitVec 64))
    (n savedIndex finalIndex : Nat) (destinationCode savedCode returnCode : HolProg 64)
    (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (handlerBitmaps : AppList (BitVec 64)) (handlerIndex : Nat) (handlerTarget : HolProg 64)
    (handlerCompile : compNative ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame) =
      (handlerTarget,(handlerBitmaps,handlerIndex)))
    (room : 3 ≤ target.stackSpace)
    (location : StackSem.locCheckExact target.code (h1,h2))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (compiled : HolProg 64)
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) (bs, n) (k, f, frame) =
      (compiled, (handlerBitmaps, handlerIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source =
      (result, sourcePost))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace - 3)
    (zero : source.clock = 0)
    (bitmapPrefix : (appListAppend handlerBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (frameSmall : f ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92) :
    stackExecutionCost (fun p _ => price p) compiled target ≤
      143 + 39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
  have handlerPrefix := (compImpIsPrefix ac false handlerCode (finalBitmaps,finalIndex)
    (k,f,frame) handlerTarget (handlerBitmaps,handlerIndex) handlerCompile).trans bitmapPrefix
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps,savedIndex)
    (k,f,frame) returnCode (finalBitmaps,finalIndex) returnCompile).trans handlerPrefix
  obtain ⟨destinationTarget,saved,header,moved,calleeCode,calleeSize,calleeBs,calleeBsPost,
    calleeIndex,calleeIndexPost,savedHandler,destinationRun,savedRun,pushRun,moveRun,
    savedRelation,prePushRelation,headerRelation,calleeCompile,calleeBitmapLength,
    calleeBitmapBound,calleeBitmapPrefix,calleeLocalsSize,found,savedLookup,headerState,
    savedSpace,movedClock,movedFfi⟩ := prepareHandlerCalleeDestination ac k f frame
      values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source target lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile lengthBound bitmapBound
      savedPrefix room location space
  have targetClock : target.clock = 0 := related.1.symm.trans zero
  have movedZero : moved.clock = 0 := movedClock.trans targetClock
  have completePrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,f,frame))
        (stackHandlerArgsNative false destination (args.length+1) (k,f,frame)))),target) =
      (none,moved) := by
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,savedRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,pushRun]
    exact moveRun
  have callCost : stackExecutionCost (fun p _ => price p)
      (.call (some (.seq .skip (copyRetNative false true (k,f,frame) values
        (popHandlerNative false (k,f,frame) returnCode)),0,l1,l2)) destination
        (some (handlerTarget,h1,h2))) {moved with clock := moved.clock+0} ≤ 12 := by
    rw [stackExecutionCost]
    simp only [Nat.add_zero,movedZero,↓reduceIte]
    exact (caps.le _).trans (by cases destination <;> simp [removalLocalPrice,nativePriceWithGap,callJumpWork])
  have bound := compiledHandlerCall_cost_from_prelude (price := price) ac k f frame values names
    retCode handlerCode l1 l2 handlerVar h1 h2 dest args bs savedBitmaps finalBitmaps handlerBitmaps
    n savedIndex finalIndex handlerIndex destinationCode savedCode returnCode handlerTarget compiled
    destination target moved target 0 none destinationCompile savedCompile returnCompile handlerCompile
    compilation completePrelude frameSmall argsSmall 12 callCost
  simp only [Nat.add_zero] at bound
  change stackExecutionCost (fun p _ => price p) compiled target ≤ _ at bound
  omega

#print axioms compiledHandlerCall_timeout_cost
end InitECandidate.Runtime.WordToStack.ExecutedHandler
