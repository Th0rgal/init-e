import InitECandidate.Runtime.WordStackReturningPreludeCost
import InitECandidate.Runtime.StackReturningCallRunCost
import InitECandidate.Runtime.WordCodeFrameBounds
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning.Execution
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- A reached callee whose frame does not fit stops at StackAlloc. Its body
and caller continuation contribute no execution cost. -/
theorem compiledCall_callee_allocation_failure_cost {F : Type}
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
    (nonzero : source.clock ≠ 0)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (insufficient : target.stackSpace < (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1))
    (frameSmall : f ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92) :
    stackExecutionCost (fun p _ => price p) compiled target ≤
      63 + 39 * Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps, savedIndex)
    (k, f, frame) returnCode (finalBitmaps, finalIndex) returnCompile).trans bitmapPrefix
  obtain ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, stack, regs, movedState⟩ :=
    prepareCalleeDestinationAt ac k f frame values names retCode l1 l2 dest args source target
      lens xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile lengthBound bitmapBound
      savedPrefix space
  have calleeSmall : calleeSize ≤ 92 := by
    obtain ⟨key, keyFound, sizeEq, _, _⟩ :=
      Flapjack.WordToStackProofs.CompCorrect.CallTail.findCode_facts dest
        (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs)
        source.code source.stackSize args1 prog ss guards.2.2.1
    exact covered.compiledFrame_le keyFound (by rw [← sizeEq]; exact calleeLocalsSize)
  have calleeInsufficient : target.stackSpace < calleeSize := by
    rw [← calleeFrameEq] at insufficient
    by_cases frameZero : calleeFrame = 0
    · simp only [frameZero, ↓reduceIte] at calleeShape insufficient
      omega
    · simp only [frameZero, ↓reduceIte] at calleeShape insufficient
      omega
  have countEq := stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k f frame destinationCode destination guards destinationCompile
  let entry := StackSemStateOps.decClock (StackSemStateOps.setVar 0 (.loc l1 l2) moved)
  have useStack : entry.useStack = true := by
    change moved.useStack = true
    rw [movedState]
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have entrySpace : entry.stackSpace = target.stackSpace - (args1.length-k) := by
    change moved.stackSpace = _
    rw [movedState]
    simp only
    rw [savedSpace, countEq]
  have allocationFailure : StackSemEvaluate.evaluate (.stackAlloc (calleeSize - (args1.length-k)), entry) =
      (some (.halt (.word (BitVec.ofNat 64 2))), StackSemStateOps.emptyEnv entry) := by
    rw [StackSemEvaluate.evaluate_stackAlloc]
    simp only [useStack, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [if_pos (by rw [entrySpace]; rw [countEq] at space; omega)]
  have calleeRun : StackSemEvaluate.evaluate (.seq (.stackAlloc (calleeSize - (args1.length-k))) body, entry) =
      (some (.halt (.word (BitVec.ofNat 64 2))), StackSemStateOps.emptyEnv entry) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, allocationFailure]
  have calleeCost : stackExecutionCost (fun p _ => price p)
      (.seq (.stackAlloc (calleeSize - (args1.length-k))) body) entry ≤ 25 := by
    rw [stackExecutionCost_seq]
    simp only [ConservativeRemovalPrice.freeSeq (price := price), Nat.zero_add, allocationFailure,
      Nat.add_zero, stackExecutionCost]
    exact ConservativeRemovalPrice.alloc _ (by omega)
  have movedNonzero : moved.clock ≠ 0 := by
    rw [movedState]
    change saved.clock ≠ 0
    rw [← savedRelation.1]
    exact nonzero
  let returnSuffix : HolProg 64 := .seq .skip (copyRetNative false false (k,f,frame) values returnCode)
  have callCost : stackExecutionCost (fun p _ => price p)
      (.call (some (returnSuffix,0,l1,l2)) destination none)
      {moved with clock := moved.clock + 0} ≤ 37 := by
    have bound := stackCost_returning_call_run (price := price) returnSuffix 0 l1 l2 destination none
      (.seq (.stackAlloc (calleeSize - (args1.length-k))) body) moved (StackSemStateOps.emptyEnv entry)
      (some (.halt (.word (BitVec.ofNat 64 2)))) movedNonzero found calleeRun
    simp only [selectedContinuationBudget, Nat.add_zero] at bound
    simp only [Nat.add_zero]
    exact bound.trans (Nat.add_le_add_right calleeCost 12)
  have completePrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (stackArgsNative destination (args.length+1) (k,f,frame))), target) =
      (none,moved) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    exact moveRun
  have bound := compiledCall_cost_from_prelude (price := price) ac k f frame values names retCode l1 l2 dest args
    bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled
    destination target moved 0 37 destinationCompile savedCompile returnCompile compilation
    frameSmall argsSmall completePrelude callCost
  simp only [Nat.add_zero] at bound
  change stackExecutionCost (fun p _ => price p) compiled target ≤ _ at bound
  omega

#print axioms compiledCall_callee_allocation_failure_cost
end InitECandidate.Runtime.WordToStack.ExecutedReturning
