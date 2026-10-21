import InitECandidate.Runtime.WordStackHandlerNormalContinuation
import InitECandidate.Runtime.StackReturningCallComposeCost
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Normal handler-call dispatch composes actual callee and restored
continuation executions at one target price and an additive cost. -/
theorem normalHandlerCallFromCallee (calleeBudget returnBudget handlerBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (originalTarget target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec 64))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (ih : InductionHypotheses price calleeBudget returnBudget handlerBudget ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult 64))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location : WordLocW 64) (returnedValues : List (WordLocW 64))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returnedValues),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.result location returnedValues)) (some (.result location)) (payload::lens))
    (moved : StackSemStateFiniteExact 64 LabToTarget.Config F) (destination : Sum Nat Nat)
    (calleeCode handlerTarget : HolProg 64) (bodyExtra : Nat)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (movedNonzero : moved.clock ≠ 0)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.result location),target))
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64)
    (compilation : compNative ac false retCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (calleeCost : stackExecutionCost (fun p _ => price p) calleeCode
      {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra} ≤ 25+calleeBudget)
    (frameSmall : frame ≤ 92)
    (returnsSmall : Compiler.Backend.WordToStack.numStackRet k values ≤ 92)
    (actualRegisters : k = 22) :
    ∃ continuationExtra targetPost targetResult,
      StackSemEvaluate.evaluate
        (.call (some (.seq .skip (copyRetNative false true (k,frame,payload) values
          (popHandlerNative false (k,frame,payload) compiled)),0,l1,l2))
          destination (some (handlerTarget,h1,h2)),
          {moved with clock := moved.clock+(bodyExtra+continuationExtra)}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens ∧
      stackExecutionCost (fun p _ => price p)
        (.call (some (.seq .skip (copyRetNative false true (k,frame,payload) values
          (popHandlerNative false (k,frame,payload) compiled)),0,l1,l2)) destination (some (handlerTarget,h1,h2)))
        {moved with clock := moved.clock+(bodyExtra+continuationExtra)} ≤
        calleeBudget+returnBudget+58+21*Compiler.Backend.WordToStack.numStackRet k values := by
  obtain ⟨gc,rest,popped,sourceFrame,keys,tailKeys,handlerEq,poppedEq,popRun,domain,
    valid,sourceContinuation,continuationIH⟩ := sourceHandlerReturningContinuation
    ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
    result xs args1 prog ss envs location returnedValues guards ih.forget nonzero wholeRun notError bodyRun
  have locationEq : location = .loc l1 l2 := by
    by_contra different
    exact valid (Or.inl different)
  obtain ⟨continuationExtra,targetPost,targetResult,continuationRun,conclusion,continuationCost⟩ :=
    simulateHandlerNormalContinuation calleeBudget returnBudget handlerBudget ac k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih conventions flat maximum nonzero result wholeRun notError location returnedValues
      bodyRun calleeSize calleeFrame bodyConclusion bs bsPost n nPost compiled compilation lengthBound
      bitmapBound bitmapPrefix labels frameSmall returnsSmall actualRegisters
  have normalRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.result (.loc l1 l2)),target) := by
    simpa only [locationEq] using calleeRun
  have skipped : StackSemEvaluate.evaluate
      (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) compiled)),
        {target with clock := target.clock+continuationExtra}) = (targetResult,targetPost) := by
    rw [CallReturnEval.seq_skip_left]
    exact continuationRun
  refine ⟨continuationExtra,targetPost,targetResult,
    returningHandlerCallNormalRun moved target targetPost l1 l2 h1 h2 bodyExtra continuationExtra
      destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) compiled))) handlerTarget targetResult
      found movedNonzero normalRun skipped,conclusion,?_⟩
  have skippedCost : stackExecutionCost (fun p _ => price p)
      (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) compiled)))
      {target with clock := target.clock+continuationExtra} ≤
      21*Compiler.Backend.WordToStack.numStackRet k values+21+returnBudget := by
    rw [stackCost_seq_skip_left (price := price)]
    exact continuationCost
  have bound := stackCost_returning_call_composeHandler (price := price) calleeCode
    (.seq .skip (copyRetNative false true (k,frame,payload) values
      (popHandlerNative false (k,frame,payload) compiled))) 0 l1 l2 destination (some (handlerTarget,h1,h2)) moved target
    bodyExtra continuationExtra (25+calleeBudget) (21*Compiler.Backend.WordToStack.numStackRet k values+21+returnBudget)
    movedNonzero found normalRun calleeCost skippedCost
  exact bound.trans (by omega)

#print axioms normalHandlerCallFromCallee
end InitECandidate.Runtime.WordToStack.ExecutedHandler
