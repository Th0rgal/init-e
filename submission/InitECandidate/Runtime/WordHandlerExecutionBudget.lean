import InitECandidate.Runtime.WordHandlerHistoryBudget
import InitECandidate.Runtime.WordHandlerCalleeBudget
namespace InitECandidate.Runtime.WordToStack.CallReturningHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.WordToStackProofs.CallReturnHandler
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-! Full installed-handler Call clock composition. Every actual callee outcome
and original resource/trace conclusion is retained; continuation budgets are
added conservatively, while zero-clock and allocation failures require zero. -/
theorem simulateSuccessfulHandlerCall (calleeBudget returnBudget handlerBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width) (destination : Sum Nat Nat)
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
    (hypotheses : InductionHypotheses calleeBudget returnBudget handlerBudget ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source) :
    ∃ extra, extra ≤ calleeBudget + returnBudget + handlerBudget ∧ ∃ targetFinal targetResult,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
        (targetResult,targetFinal) ∧
      compCorrectResult ac k frame payload source sourcePost targetFinal result targetResult lens := by
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
    calleeSize,calleeFrame,bodyExtra,bodyBound,targetResult,destinationRun,savedRun,pushRun,argumentsRun,
    found,calleeShape,allocationRun,bodyTargetRun,calleeRun,bodyConclusion⟩ :=
    simulateHandlerCalleeBody calleeBudget returnBudget handlerBudget ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source sourcePost bodyPost result bodyResult target lens xs args1 prog ss envs bs
      savedBitmaps n savedIndex destinationCode savedCode destination guards related conventions maximum
      destinationCompile savedCompile bitmapLength bitmapBound savedPrefix room handlerLocation space
      nonzero wholeExecution notError bodyRun hypotheses
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
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
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
      ∃ extra, extra ≤ calleeBudget + returnBudget + handlerBudget ∧ ∃ targetFinal finalResult,
        StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
          (finalResult,targetFinal) ∧
        compCorrectResult ac k frame payload source sourcePost targetFinal result finalResult lens := by
    obtain ⟨callRun,conclusion⟩ := terminalHandlerCallFromCallee ac k frame payload calleeSize calleeFrame
      values names retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost
      result bodyResult target moved calleeTarget targetResult lens xs args1 prog ss envs bodyExtra
      destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode))) handlerTarget guards related nonzero
      wholeExecution bodyRun found movedNonzero calleeRun bodyConclusion terminal
    exact ⟨bodyExtra,by omega,calleeTarget,targetResult,
      completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
        h1 h2 dest args bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode
        savedCode returnCode handlerTarget compiled destination target moved calleeTarget bodyExtra targetResult
        destinationCompile savedCompile returnCompile handlerCompile compilation preludeRun callRun,conclusion⟩
  by_cases matching : bodyResult.map compileResult = targetResult
  · have outcomes := handlerCalleeOutcomeCases values names retCode handlerCode l1 l2 handlerVar h1 h2
      dest args source sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero
      wholeExecution bodyRun notError
    rcases outcomes with ⟨location,returned,rfl⟩ | ⟨location,value,rfl⟩ | timeout | resource | ⟨event,ffi⟩
    · have targetEq : targetResult = some (.result location) := by
        simpa only [Option.map_some,compileResult] using matching.symm
      subst targetResult
      exact normalCompiledHandlerCallFromHistory calleeBudget returnBudget handlerBudget ac k frame payload source sourcePost bodyPost target
        calleeTarget lens related values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1
        prog ss envs guards hypotheses conventions flat maximum nonzero result wholeExecution notError
        location returned bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode
        bodyExtra bodyBound found calleeRun bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex
        destinationCode savedCode returnCode handlerTarget compiled destinationCompile savedCompile
        returnCompile handlerCompile compilation bitmapLength bitmapBound bitmapPrefix labels preludeRun
    · have targetEq : targetResult = some (.exception location) := by
        simpa only [Option.map_some,compileResult] using matching.symm
      subst targetResult
      exact exceptionCompiledHandlerCallFromHistory calleeBudget returnBudget handlerBudget ac k frame payload source sourcePost bodyPost target
        calleeTarget lens related values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1
        prog ss envs guards hypotheses conventions flat maximum nonzero result wholeExecution notError
        location value bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode
        bodyExtra bodyBound found calleeRun bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex
        destinationCode savedCode returnCode handlerTarget compiled destinationCompile savedCompile
        returnCompile handlerCompile compilation bitmapLength bitmapBound bitmapPrefix labels preludeRun
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

theorem simulateHandlerCallWithGuards (calleeBudget returnBudget handlerBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width) (destination : Sum Nat Nat)
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
    (wholeExecution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (hypotheses : InductionHypotheses calleeBudget returnBudget handlerBudget ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source) :
    ∃ extra, extra ≤ calleeBudget + returnBudget + handlerBudget ∧ ∃ targetFinal targetResult,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
        (targetResult,targetFinal) ∧
      compCorrectResult ac k frame payload source sourcePost targetFinal result targetResult lens := by
  by_cases room : 3 ≤ target.stackSpace
  · by_cases arguments : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
        target.stackSpace-3
    · by_cases zero : source.clock = 0
      · have location : StackSem.locCheckExact target.code (h1,h2) := by
          apply labels (h1,h2)
          have shape := compilation
          simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
            Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
          obtain ⟨rfl,_⟩ := shape
          simp only [StackSem.getLabelsExact,or_true,true_or]
        obtain ⟨targetPost,run,contract⟩ := compiledHandlerCallTimeout ac k frame payload values names
          retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost result target lens xs
          args1 prog ss envs bs savedBitmaps retBs n savedIndex retIndex destinationCode savedCode
          returnCode destination guards related conventions maximum destinationCompile savedCompile
          returnCompile handlerBs handlerIndex handlerTarget handlerCompile room location bitmapLength
          bitmapBound compiled compilation wholeExecution arguments zero bitmapPrefix
        refine ⟨0,Nat.zero_le _,targetPost,some .timeOut,?_,contract⟩
        have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
        rwa [unchanged]
      · by_cases calleeSpace : (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
            else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1) ≤ target.stackSpace-3
        · rcases bodyRun : WordSemStateFiniteExact.evaluate prog
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
                (WordSemStateFiniteExact.decClock source))) with ⟨bodyResult,bodyPost⟩
          exact simulateSuccessfulHandlerCall calleeBudget returnBudget handlerBudget ac k frame payload values names retCode l1 l2 dest args
            handlerVar h1 h2 handlerCode source sourcePost bodyPost result bodyResult target lens xs args1
            prog ss envs bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode
            savedCode returnCode handlerTarget compiled destination guards related conventions flat maximum
            destinationCompile savedCompile returnCompile handlerCompile compilation bitmapLength bitmapBound
            bitmapPrefix labels room calleeSpace zero wholeExecution notError bodyRun hypotheses
        · obtain ⟨targetPost,run,contract⟩ := compiledHandlerCalleeAllocationFailure ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
            handlerCode source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps retBs
            n savedIndex retIndex destinationCode savedCode returnCode destination guards related conventions
            maximum destinationCompile savedCompile returnCompile handlerBs handlerIndex handlerTarget compiled
            handlerCompile compilation wholeExecution bitmapLength bitmapBound bitmapPrefix labels
            room arguments zero (by omega)
          refine ⟨0,Nat.zero_le _,targetPost,some (.halt (.word 2)),?_,contract⟩
          have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
          rwa [unchanged]
    · obtain ⟨targetPost,run,contract⟩ := compiledHandlerArgumentsFailure ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
        handlerCode source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps retBs
        n savedIndex retIndex destinationCode savedCode returnCode destination guards related conventions
        maximum destinationCompile savedCompile returnCompile handlerBs handlerIndex handlerTarget compiled
        handlerCompile compilation wholeExecution bitmapLength bitmapBound bitmapPrefix labels
        room (by omega)
      refine ⟨0,Nat.zero_le _,targetPost,some (.halt (.word 2)),?_,contract⟩
      have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
      rwa [unchanged]
  · obtain ⟨targetPost,run,contract⟩ := compiledHandlerHeaderFailure ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps retBs
      n savedIndex retIndex destinationCode savedCode returnCode destination guards related conventions
      maximum destinationCompile savedCompile returnCompile handlerBs handlerIndex handlerTarget compiled
      handlerCompile compilation wholeExecution bitmapLength bitmapBound bitmapPrefix (by omega)
    refine ⟨0,Nat.zero_le _,targetPost,some (.halt (.word 2)),?_,contract⟩
    have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
    rwa [unchanged]

/-- The entire original comp_correct induction motive for a returning Call
with SOME handler. Source guards and all native compiler subtrees are derived
from the actual source execution and whole compilation. Every resource and
clock branch is covered and every actual callee outcome uses only the original
guarded IHs. This full constructor assembly is untagged pending independent
source statement review; it assumes no target execution or final relation. -/
theorem returningHandlerCase (calleeBudget returnBudget handlerBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (hypotheses : InductionHypotheses calleeBudget returnBudget handlerBudget ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source) :
    BoundedSimulation ac (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) source (calleeBudget + returnBudget + handlerBudget) := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens facts
  obtain ⟨execution,notError,related,conventions,flat,compilation,lengthBound,bitmapBound,
    bitmapPrefix,labels,maximum⟩ := facts
  obtain ⟨xs,args1,prog,ss,envs,guards⟩ := sourceGuardsOfNotErrorWithHandler values names retCode
    l1 l2 dest args (some (handlerVar,handlerCode,h1,h2)) source sourcePost result execution notError
  rcases destinationCompile : callDestNative (width := width) dest args (k,f,frame) with ⟨destinationCode,destination⟩
  rcases savedCompile : wLiveNative (width := width) names (bs,n) (k,f,frame) with ⟨savedCode,savedBitmaps,savedIndex⟩
  rcases returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,f,frame) with
    ⟨returnCode,retBs,retIndex⟩
  rcases handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,f,frame) with
    ⟨handlerTarget,handlerBs,handlerIndex⟩
  have shape := compilation
  simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
    Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
  obtain ⟨_,rfl,rfl⟩ := shape
  exact simulateHandlerCallWithGuards calleeBudget returnBudget handlerBudget ac k f frame values names retCode l1 l2 dest args
    handlerVar h1 h2 handlerCode source sourcePost result target lens xs args1 prog ss envs bs
    savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
    returnCode handlerTarget compiled destination guards related conventions flat maximum
    destinationCompile savedCompile returnCompile handlerCompile compilation lengthBound bitmapBound
    bitmapPrefix labels execution notError hypotheses


#print axioms returningHandlerCase
end InitECandidate.Runtime.WordToStack.CallReturningHandler
