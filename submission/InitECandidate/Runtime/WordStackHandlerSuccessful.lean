import InitECandidate.Runtime.WordStackHandlerCallee
import InitECandidate.Runtime.WordStackHandlerNormalHistory
import InitECandidate.Runtime.WordStackHandlerExceptionHistory
import InitECandidate.Runtime.StackReturningCallPropagateCost
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Every successful-allocation handler-call outcome retains the original
semantic/resource contract and its actual executed additive cost. -/
theorem simulateSuccessfulHandlerCall (calleeBudget returnBudget handlerBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec 64))
    (source sourcePost bodyPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (result bodyResult : Option (WordSemResult 64))
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (bs savedBitmaps retBs handlerBs : AppList (BitVec 64))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg 64) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k frame payload source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * payload + 2 * k)
    (destinationCompile : callDestNative dest args (k, frame, payload) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, frame, payload) = (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (room : 3 ≤ target.stackSpace)
    (space : (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1) ≤ target.stackSpace-3)
    (nonzero : source.clock ≠ 0)
    (wholeExecution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) = (bodyResult,bodyPost))
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (frameSmall : frame ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92)
    (returnsSmall : Compiler.Backend.WordToStack.numStackRet k values ≤ 92)
    (actualRegisters : k = 22)
    (hypotheses : InductionHypotheses price calleeBudget returnBudget handlerBudget ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source) :
    ∃ extra targetFinal targetResult,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
        (targetResult,targetFinal) ∧
      compCorrectResult ac k frame payload source sourcePost targetFinal result targetResult lens ∧
      stackExecutionCost (fun p _ => price p) compiled {target with clock := target.clock+extra} ≤
      calleeBudget+189+39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k+
        (match (generalizing := false) bodyResult with
         | some (.result _ _) => returnBudget+21*Compiler.Backend.WordToStack.numStackRet k values
         | some (.exception _ _) => handlerBudget
         | _ => 0) := by
  have returnPrefix := compImpIsPrefix ac false retCode (savedBitmaps,savedIndex) (k,frame,payload)
    returnCode (retBs,retIndex) returnCompile
  have handlerPrefix := compImpIsPrefix ac false handlerCode (retBs,retIndex) (k,frame,payload)
    handlerTarget (handlerBs,handlerIndex) handlerCompile
  have savedPrefix := returnPrefix.trans (handlerPrefix.trans bitmapPrefix)
  have handlerLocation : StackSem.locCheckExact target.code (h1,h2) := by
    apply labels (h1,h2)
    have shape := compilation
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
      Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
    obtain ⟨rfl,_⟩ := shape
    simp only [StackSem.getLabelsExact,or_true,true_or]
  obtain ⟨destinationTarget,saved,header,moved,entry,calleeTarget,calleeCode,body,
    calleeSize,calleeFrame,bodyExtra,targetResult,destinationRun,savedRun,pushRun,argumentsRun,
    found,calleeShape,allocationRun,bodyTargetRun,calleeRun,bodyConclusion,bodyCost,calleeCost⟩ :=
    simulateHandlerCalleeBody (price := price) calleeBudget returnBudget handlerBudget ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source sourcePost bodyPost result bodyResult target lens xs args1 prog ss envs bs
      savedBitmaps n savedIndex destinationCode savedCode destination guards related conventions maximum
      destinationCompile savedCompile bitmapLength bitmapBound savedPrefix room handlerLocation space
      nonzero wholeExecution notError bodyRun covered actualRegisters hypotheses
  have preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target) =
      (none,moved) := by
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,savedRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,pushRun]
    exact argumentsRun
  have free := completeHandlerPreludeClockFree (C := LabToTarget.Config) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBitmaps,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free target target.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target) =
    (Prod.map id (fun state => {state with clock := target.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
          (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = target.clock := congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by rw [clockEq,← related.1]; exact nonzero
  have finishTerminal
      (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
        ∃ event, targetResult = some (.finalFFI event)) :
      ∃ extra targetFinal finalResult,
        StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
          (finalResult,targetFinal) ∧
        compCorrectResult ac k frame payload source sourcePost targetFinal result finalResult lens ∧
        stackExecutionCost (fun p _ => price p) compiled {target with clock := target.clock+extra} ≤
        calleeBudget+189+39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k+
        (match (generalizing := false) bodyResult with
         | some (.result _ _) => returnBudget+21*Compiler.Backend.WordToStack.numStackRet k values
         | some (.exception _ _) => handlerBudget
         | _ => 0) := by
    obtain ⟨callRun,conclusion⟩ := terminalHandlerCallFromCallee ac k frame payload calleeSize calleeFrame
      values names retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost
      result bodyResult target moved calleeTarget targetResult lens xs args1 prog ss envs bodyExtra
      destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode))) handlerTarget guards related nonzero
      wholeExecution bodyRun found movedNonzero calleeRun bodyConclusion terminal
    refine ⟨bodyExtra,calleeTarget,targetResult,
      completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
        h1 h2 dest args bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode
        savedCode returnCode handlerTarget compiled destination target moved calleeTarget bodyExtra targetResult
        destinationCompile savedCompile returnCompile handlerCompile compilation preludeRun callRun,conclusion,?_⟩
    have selectedZero : ∀ returnBudget handlerBudget,
        selectedContinuationBudget targetResult l1 l2 (some (handlerTarget,h1,h2)) returnBudget handlerBudget = 0 := by
      intro retPrice handlerPrice
      rcases terminal with rfl | ⟨value,rfl⟩ | ⟨event,rfl⟩ <;> rfl
    have callCost := stackCost_returning_call_propagateSelected (price := price) calleeCode
      (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode))) 0 l1 l2 destination
      (some (handlerTarget,h1,h2)) moved calleeTarget targetResult bodyExtra (25+calleeBudget)
      movedNonzero found selectedZero calleeRun calleeCost
    have bounded := compiledHandlerCall_cost_from_prelude (price := price) ac k frame payload values names
      retCode handlerCode l1 l2 handlerVar h1 h2 dest args bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex
      destinationCode savedCode returnCode handlerTarget compiled destination target moved calleeTarget bodyExtra targetResult
      destinationCompile savedCompile returnCompile handlerCompile compilation preludeRun frameSmall argsSmall
      (25+calleeBudget+12) callCost
    exact bounded.trans (by omega)
  by_cases matching : bodyResult.map compileResult = targetResult
  · have outcomes := handlerCalleeOutcomeCases values names retCode handlerCode l1 l2 handlerVar h1 h2
      dest args source sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero
      wholeExecution bodyRun notError
    rcases outcomes with ⟨location,returned,rfl⟩ | ⟨location,value,rfl⟩ | timeout | resource | ⟨event,ffi⟩
    · have targetEq : targetResult = some (.result location) := by
        simpa only [Option.map_some,compileResult] using matching.symm
      subst targetResult
      obtain ⟨extra, final, output, run, relation, cost⟩ := normalCompiledHandlerCallFromHistory (price := price)
        calleeBudget returnBudget handlerBudget ac k frame payload source sourcePost bodyPost target
        calleeTarget lens related values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1
        prog ss envs guards hypotheses conventions flat maximum nonzero result wholeExecution notError
        location returned bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode
        bodyExtra found calleeRun bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex
        destinationCode savedCode returnCode handlerTarget compiled destinationCompile savedCompile
        returnCompile handlerCompile compilation bitmapLength bitmapBound bitmapPrefix labels preludeRun calleeCost frameSmall argsSmall returnsSmall actualRegisters
      refine ⟨extra, final, output, run, relation, ?_⟩
      simp only
      exact cost.trans (by omega)
    · have targetEq : targetResult = some (.exception location) := by
        simpa only [Option.map_some,compileResult] using matching.symm
      subst targetResult
      obtain ⟨extra, final, output, run, relation, cost⟩ := exceptionCompiledHandlerCallFromHistory (price := price)
        calleeBudget returnBudget handlerBudget ac k frame payload source sourcePost bodyPost target
        calleeTarget lens related values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1
        prog ss envs guards hypotheses conventions flat maximum nonzero result wholeExecution notError
        location value bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode
        bodyExtra found calleeRun bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex
        destinationCode savedCode returnCode handlerTarget compiled destinationCompile savedCompile
        returnCompile handlerCompile compilation bitmapLength bitmapBound bitmapPrefix labels preludeRun calleeCost frameSmall argsSmall actualRegisters
      refine ⟨extra, final, output, run, relation, ?_⟩
      simp only
      exact cost.trans (by omega)
    · apply finishTerminal
      left
      simpa only [timeout,Option.map_some,compileResult] using matching.symm
    · apply finishTerminal
      right; left
      exact ⟨.word 1,by simpa only [resource,Option.map_some,compileResult] using matching.symm⟩
    · apply finishTerminal
      right; right
      exact ⟨event,by simpa only [ffi,Option.map_some,compileResult] using matching.symm⟩
  · have mismatch := bodyConclusion
    unfold compCorrectResult at mismatch
    rw [if_pos matching] at mismatch
    exact finishTerminal (Or.inr (Or.inl ⟨.word 2,mismatch.1⟩))

#print axioms simulateSuccessfulHandlerCall
end InitECandidate.Runtime.WordToStack.ExecutedHandler
