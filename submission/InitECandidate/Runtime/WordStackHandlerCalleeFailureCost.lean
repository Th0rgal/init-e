import InitECandidate.Runtime.StackReturningCallRunCost
import InitECandidate.Runtime.WordCodeFrameBounds
import InitECandidate.Runtime.WordStackHandlerPreludeCost
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler.Execution
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]


/-- Failed callee allocation executes no body or continuation. -/
theorem compiledHandlerCalleeAllocationFailure_cost {F : Type}
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
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (room : 3 ≤ target.stackSpace)
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
      target.stackSpace - 3)
    (nonzero : source.clock ≠ 0)
    (insufficient : target.stackSpace - 3 <
      (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
       else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1))
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (frameSmall : f ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92) :
    stackExecutionCost (fun p _ => price p) compiled target ≤
      168+39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
  have retPrefix := (compImpIsPrefix ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame)
    handlerTarget (handlerBs,handlerIndex) handlerCompile).trans bitmapPrefix
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps,savedIndex) (k,f,frame)
    returnCode (finalBitmaps,finalIndex) returnCompile).trans retPrefix
  have location : StackSem.locCheckExact target.code (h1,h2) := by
    apply labels (h1,h2)
    have shape := compilation
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
      Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
    obtain ⟨rfl,_⟩ := shape
    simp only [StackSem.getLabelsExact,or_true,true_or]
  obtain ⟨destinationTarget,saved,header,moved,calleeCode,calleeSize,calleeBs,calleePostBs,
    calleeIndex,calleePostIndex,savedHandler,destinationRun,savedRun,pushRun,moveRun,
    savedRelation,prePushRelation,headerRelation,calleeCompile,_,_,_,localSize,found,
    savedLookup,headerState,savedSpace,movedClock,movedFfi⟩ :=
    prepareHandlerCalleeDestination ac k f frame values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source target lens xs args1 prog ss envs bs savedBitmaps n savedIndex
      destinationCode savedCode destination guards related conventions maximum destinationCompile
      savedCompile lengthBound bitmapBound savedPrefix room location space
  obtain ⟨body,calleeFrame,calleeShape,_,frameShape,capacity,_,frameDef⟩ := calleeBodyCompilation ac k
    args1.length prog calleeBs calleePostBs calleeIndex calleePostIndex calleeCode calleeSize calleeCompile
  have sizeDef : calleeSize = if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1 := by
    rw [← frameDef]
    by_cases zero : calleeFrame = 0
    · simpa only [zero,if_true] using frameShape
    · simpa only [zero,if_false] using frameShape
  have count := CallReturning.stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k f frame destinationCode destination guards destinationCompile
  have savedUseStack : saved.useStack = true := savedRelation.2.2.2.2.1
  have savedBound := savedRelation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have moveBound := CallReturning.stackArgumentFrameBound ac k f frame values names retCode l1 l2
    dest args source saved lens xs args1 prog ss envs destinationCode destination guards savedRelation
    (conventionsWithoutHandler k values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2)) conventions)
    (lt_of_le_of_lt (maximumWithoutHandler values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2))) maximum) destinationCompile
  have savedRoom : 3 ≤ saved.stackSpace := by omega
  have resources := CallReturnHandler.pushedHandlerStateResources saved h1 h2 k savedHandler savedRoom
  have headerSpace : header.stackSpace+3 = target.stackSpace := by
    rw [headerState]
    omega
  obtain ⟨moved',stack,regs,moveRun',movedState,_,_,movedSpace,_,_⟩ := evaluateHandlerArguments
    k f frame h1 h2 destination (args.length+1) saved savedHandler savedUseStack savedRoom savedBound
    moveBound (by rw [← headerState]; omega)
  rw [← headerState] at moveRun' movedState movedSpace
  have sameMoved : moved' = moved := (Prod.mk.inj (moveRun'.symm.trans moveRun)).2
  rw [sameMoved] at movedState movedSpace
  have movedUseStack : moved.useStack = true := by
    rw [movedState,headerState]
    exact savedUseStack
  have calleeInsufficient : header.stackSpace < calleeSize := by rw [sizeDef]; omega
  have allocInsufficient : moved.stackSpace < calleeSize-(args1.length-k) := by
    rw [count] at movedSpace
    split at frameShape <;> omega
  have movedNonzero : moved.clock ≠ 0 := by
    rw [movedClock,← related.1]
    exact nonzero
  let entry := StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)
  have entryUse : entry.useStack = true := movedUseStack
  have entryInsufficient : entry.stackSpace < calleeSize-(args1.length-k) := allocInsufficient
  have calleeRun : StackSemEvaluate.evaluate (calleeCode,entry) =
      (some (.halt (.word (BitVec.ofNat 64 2))),StackSemStateOps.emptyEnv entry) := by
    rw [calleeShape,StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_stackAlloc]
    simp only [entryUse,Bool.not_true,Bool.false_eq_true,if_false,entryInsufficient,if_true]
  have calleeSmall : calleeSize ≤ 92 := by
    obtain ⟨key,keyFound,sizeEq,_,_⟩ := CallTail.findCode_facts dest
      (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs)
      source.code source.stackSize args1 prog ss guards.2.2.1
    exact covered.compiledFrame_le keyFound (by rw [← sizeEq]; exact localSize)
  have allocationFailure : StackSemEvaluate.evaluate
      (.stackAlloc (calleeSize-(args1.length-k)),entry) =
      (some (.halt (.word (BitVec.ofNat 64 2))),StackSemStateOps.emptyEnv entry) := by
    rw [StackSemEvaluate.evaluate_stackAlloc]
    change (if !moved.useStack then _ else if moved.stackSpace < _ then _ else _) = _
    simp only [movedUseStack,Bool.not_true,Bool.false_eq_true,if_false,allocInsufficient,if_true]
  have calleeCost : stackExecutionCost (fun p _ => price p) calleeCode entry ≤ 25 := by
    rw [calleeShape,stackExecutionCost_seq]
    simp only [ConservativeRemovalPrice.freeSeq (price := price),Nat.zero_add,allocationFailure,
      Nat.add_zero,stackExecutionCost]
    exact ConservativeRemovalPrice.alloc _ (by omega)
  let returnSuffix : HolProg 64 := .seq .skip (copyRetNative false true (k,f,frame) values
    (popHandlerNative false (k,f,frame) returnCode))
  have callCost : stackExecutionCost (fun p _ => price p)
      (.call (some (returnSuffix,0,l1,l2)) destination (some (handlerTarget,h1,h2)))
      {moved with clock := moved.clock+0} ≤ 37 := by
    have bound := stackCost_returning_call_run (price := price) returnSuffix 0 l1 l2 destination
      (some (handlerTarget,h1,h2)) calleeCode moved (StackSemStateOps.emptyEnv entry)
      (some (.halt (.word (BitVec.ofNat 64 2)))) movedNonzero found calleeRun
    simp only [selectedContinuationBudget,Nat.add_zero] at bound
    simp only [Nat.add_zero]
    exact bound.trans (Nat.add_le_add_right calleeCost 12)
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
  have bound := compiledHandlerCall_cost_from_prelude (price := price) ac k f frame values names
    retCode handlerCode l1 l2 handlerVar h1 h2 dest args bs savedBitmaps finalBitmaps handlerBs
    n savedIndex finalIndex handlerIndex destinationCode savedCode returnCode handlerTarget compiled
    destination target moved target 0 none destinationCompile savedCompile returnCompile handlerCompile
    compilation completePrelude frameSmall argsSmall 37 callCost
  simp only [Nat.add_zero] at bound
  change stackExecutionCost (fun p _ => price p) compiled target ≤ _ at bound
  omega

#print axioms compiledHandlerCalleeAllocationFailure_cost
end InitECandidate.Runtime.WordToStack.ExecutedHandler
