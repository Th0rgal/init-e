import InitECandidate.Runtime.WordStackHandlerStoppedPrelude
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler.Execution
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Insufficient room for the handler header stops before arguments/callee.
The original compiler relation derives the stopped prefix and its cost. -/
theorem compiledHandlerHeaderFailure_cost {F : Type}
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
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (handlerBs : AppList (BitVec 64)) (handlerIndex : Nat)
    (handlerTarget compiled : HolProg 64)
    (handlerCompile : compNative ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,f,frame) =
      (compiled,(handlerBs,handlerIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (noRoom : target.stackSpace < 3)
    (frameSmall : f ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92) :
    stackExecutionCost (fun p _ => price p) compiled target ≤
      131+39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
  have retPrefix := (compImpIsPrefix ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame)
    handlerTarget (handlerBs,handlerIndex) handlerCompile).trans bitmapPrefix
  obtain ⟨targetPost,headerRun,ffi⟩ := evaluateHandlerHeaderNoRoom ac k f frame values names retCode
    l1 l2 dest args handlerVar h1 h2 handlerCode source target lens xs args1 prog ss envs bs
    savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode destination
    guards related conventions maximum destinationCompile savedCompile returnCompile lengthBound
    bitmapBound retPrefix noRoom
  have stoppedPrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,f,frame))
        (stackHandlerArgsNative false destination (args.length+1) (k,f,frame)))),target) =
      (some (.halt (.word (BitVec.ofNat 64 2))),targetPost) := by
    rw [Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
      Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
      StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,headerRun]
  exact compiledHandlerCall_cost_stopped_prelude (price := price) ac k f frame values names retCode handlerCode
    l1 l2 handlerVar h1 h2 dest args bs savedBitmaps finalBitmaps handlerBs n savedIndex finalIndex handlerIndex
    destinationCode savedCode returnCode handlerTarget compiled destination target targetPost
    (.halt (.word (BitVec.ofNat 64 2))) destinationCompile savedCompile returnCompile handlerCompile compilation
    stoppedPrelude frameSmall argsSmall

#print axioms compiledHandlerHeaderFailure_cost
end InitECandidate.Runtime.WordToStack.ExecutedHandler
