import InitECandidate.Runtime.WordStackHandlerMotive
import InitECandidate.Runtime.WordStackHandlerRestoreCost
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Actual normal-return handler restoration composes the reached continuation
cost, preserving the full original caller/resource relation. -/
theorem simulateHandlerNormalContinuation (calleeBudget returnBudget handlerBudget : Nat) {F : Type}
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
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64)
    (compilation : compNative ac false retCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (frameSmall : frame ≤ 92)
    (returnsSmall : Compiler.Backend.WordToStack.numStackRet k values ≤ 92)
    (actualRegisters : k = 22) :
    ∃ extraClock targetPost targetResult,
      StackSemEvaluate.evaluate
        (copyRetNative false true (k,frame,payload) values
          (popHandlerNative false (k,frame,payload) compiled),
          {target with clock := target.clock+extraClock}) = (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens ∧
      stackExecutionCost (fun p _ => price p)
        (copyRetNative false true (k,frame,payload) values (popHandlerNative false (k,frame,payload) compiled))
        {target with clock := target.clock+extraClock} ≤
        21*Compiler.Backend.WordToStack.numStackRet k values + 21 + returnBudget := by
  obtain ⟨gc,rest,popped,sourceFrame,keys,tailKeys,handlerEq,poppedEq,popRun,domain,
    valid,sourceContinuation,semanticIH⟩ := sourceHandlerReturningContinuation
      ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
      result xs args1 prog ss envs location returnedValues guards ih.forget nonzero wholeRun notError bodyRun
  have continuationIH := ih.1 xs args1 prog ss envs location returnedValues bodyPost popped
    ⟨guards,nonzero,bodyRun,valid,popRun,domain⟩
  have lengthEq : returnedValues.length = values.length := by omega
  obtain ⟨restoredSource,restored,restoredPop,restoreRun,restoredRelation⟩ :=
    restoreHandlerCallerFromBodyReturn ac k frame payload source bodyPost originalTarget target lens prior
      values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs guards
      conventions maximum location returnedValues lengthEq bodyRun calleeSize calleeFrame bodyConclusion
  have sourceSame : restoredSource = popped := Option.some.inj (restoredPop.symm.trans popRun)
  rw [sourceSame] at restoredRelation
  have mono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (copyRetNative false true (k,frame,payload) values
      (popHandlerNative false (k,frame,payload) .skip)) target restored none restoreRun
  have restoredBitmapBound : n-(appListAppend bs).length ≤ restored.bitmaps.length :=
    bitmapBound.trans mono.1.length_le
  have restoredBitmapPrefix : (appListAppend bsPost).IsPrefix
      (restored.bitmaps.drop (n-(appListAppend bs).length)) := bitmapPrefix.trans (mono.1.drop _)
  have restoredLabels : ∀ loc, StackSem.getLabelsExact compiled loc →
      StackSem.locCheckExact restored.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset target.code restored.code mono.2 loc (labels loc member)
  have retConventions := (CallReturning.returningConventions k values names retCode l1 l2 dest args
    (conventionsWithoutHandler k values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2)) conventions)).1
  have retFlat : flatExpConventions retCode = true := by
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    exact flat.1
  have retMax : maxVarHOL retCode < 2*payload+2*k := by
    simp only [maxVarHOL,Flapjack.WordAlloc.max3Eq] at maximum
    omega
  obtain ⟨extraClock,targetPost,targetResult,continuationRun,conclusion,continuationCost⟩ :=
    continuationIH k frame payload sourcePost restored result bs bsPost n nPost compiled lens
      ⟨sourceContinuation,notError,restoredRelation,retConventions,retFlat,compilation,
        lengthBound,restoredBitmapBound,restoredBitmapPrefix,restoredLabels,retMax⟩ frameSmall
  have extendedRestore := Compiler.Backend.StackProps.evaluateAddClock extraClock
    (copyRetNative false true (k,frame,payload) values
      (popHandlerNative false (k,frame,payload) .skip)) target none restored ⟨restoreRun,by simp⟩
  have sourceHandler : (WordSemStateFiniteExact.setVars values returnedValues popped).handler =
      source.handler := by rw [poppedEq]; rfl
  refine ⟨extraClock,targetPost,targetResult,?_,?_,?_⟩
  · rw [handlerRestoreContinuationSequence,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,extendedRestore]
    exact continuationRun
  · unfold compCorrectResult at conclusion ⊢
    rw [sourceHandler] at conclusion
    exact conclusion

  · rw [stackCost_handler_restore_sequence (price := price)]
    have prefixCost := wordStack_handler_restore_prefix_cost (price := price) k frame payload values
      frameSmall returnsSmall {target with clock := target.clock+extraClock}
    have bound := stackCost_seq_run (price := price)
      (copyRetNative false true (k,frame,payload) values (popHandlerNative false (k,frame,payload) .skip))
      compiled {target with clock := target.clock+extraClock} {restored with clock := restored.clock+extraClock}
      (21*Compiler.Backend.WordToStack.numStackRet k values + 21) extendedRestore prefixCost
    exact bound.trans (Nat.add_le_add_left (continuationCost actualRegisters) _)

#print axioms simulateHandlerNormalContinuation
end InitECandidate.Runtime.WordToStack.ExecutedHandler
