import InitECandidate.Runtime.WordReturningBudgets
namespace InitECandidate.Runtime.WordToStack.CallReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-! The actual caller restoration and return-copy preserve the reached
continuation's extra-clock ceiling and full original result/resource relation. -/
theorem restoreCallerFromBodyReturn (calleeBudget returnBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (ih : InductionHypotheses calleeBudget returnBudget ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost target (some (.result location returned)) (some (.result location)) (frame :: lens)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F),
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      WordSemStateFiniteExact.evaluate retCode (WordSemStateFiniteExact.setVars values returned popped) =
        (result, sourcePost) ∧
      BoundedSimulation ac retCode (WordSemStateFiniteExact.setVars values returned popped) returnBudget ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, target) = (none, restored) ∧
      stateRel ac k callerSize frame
        (WordSemStateFiniteExact.setVars values returned popped) restored lens 0 := by
  obtain ⟨gc, tail, popped, sourceFrame, _, _, _, popShape, popRun, domain,
    valid, continuationRun, originalContinuationIH⟩ :=
    sourceReturningContinuation ac values names retCode l1 l2 dest args source sourcePost
      bodyPost result xs args1 prog ss envs location returned guards ih.forget nonzero execution
      notError bodyRun
  have continuationIH := ih.1 xs args1 prog ss envs location returned bodyPost popped
    ⟨guards, nonzero, bodyRun, valid, popRun, domain⟩
  have kBound : 4 < k := by
    have h := callerRelation
    unfold stateRel at h
    aesop (config := { enableSimp := false })
  obtain ⟨positive, canonical, nameBound, physical⟩ :=
    returningCallerLocalObligations k frame values names retCode l1 l2 dest args source
      xs args1 prog ss envs popped.locals guards conventions maximum (by omega) domain
  have callerShape : if frame = 0 then callerSize = 0 else callerSize = frame + 1 := by
    have h := callerRelation
    unfold stateRel at h
    aesop (config := { enableSimp := false })
  have callerSizeEq : callerSize = frame + 1 := by
    rw [if_neg (by omega)] at callerShape
    exact callerShape
  have lengthEq := (not_or.mp valid).2
  have countEq : returned.length - (k - 1) =
      Compiler.Backend.WordToStack.numStackRet k values := by
    unfold Compiler.Backend.WordToStack.numStackRet
    omega
  simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
    not_true_eq_false, ↓reduceIte] at bodyConclusion
  obtain ⟨bodyRelation, placements⟩ := bodyConclusion
  rw [countEq] at bodyRelation
  subst popped
  obtain ⟨restored, copyRun, restoredRelation⟩ :=
    copyReturnRestoresCallerState ac k frame bodyPost target source.localsSize
      (sptToAList envs.1) gc tail lens values returned (by omega) canonical
      (by omega) (by omega) physical sourceFrame bodyRelation placements
  refine ⟨_, restored, popRun, continuationRun, continuationIH, ?_, ?_⟩
  · rwa [callerSizeEq]
  · rw [callerSizeEq]
    exact restoredRelation

theorem executeReturningContinuation (calleeBudget returnBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (values : List Nat)
    (retCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target restored : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (ih : BoundedSimulation ac retCode source returnBudget)
    (sourceRun : WordSemStateFiniteExact.evaluate retCode source = (result, sourcePost))
    (notError : result ≠ some .error)
    (related : stateRel ac k f frame source restored lens 0)
    (conventions : postAllocConventionsHOL k retCode = true)
    (flat : flatExpConventions retCode = true)
    (compilation : compNative ac false retCode (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ restored.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (restored.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact restored.code loc)
    (maximum : maxVarHOL retCode < 2 * frame + 2 * k)
    (copyRun : StackSemEvaluate.evaluate
      (copyRetNative false false (k, f, frame) values .skip, target) = (none, restored)) :
    ∃ (extraClock : Nat), extraClock ≤ returnBudget ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, f, frame) values compiled,
          {target with clock := target.clock + extraClock}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨extraClock, bound, targetPost, targetResult, continuationRun, conclusion⟩ :=
    ih k f frame sourcePost restored result bs bsPost n nPost compiled lens
      ⟨sourceRun, notError, related, conventions, flat, compilation, lengthBound,
        bitmapBound, bitmapPrefix, labels, maximum⟩
  have clockFree := returnCopyClockFree (width := width) (C := C) (F := F) k f frame values
  have sameClock := clockFree target target.clock
  rw [show {target with clock := target.clock} = target from rfl, copyRun] at sameClock
  simp only [Prod.map, id_eq, Prod.mk.injEq] at sameClock
  have clockEq : restored.clock = target.clock := by
    have projected := congrArg
      (fun state : StackSemStateFiniteExact width C F => state.clock) sameClock.2
    exact projected
  have clockedCopy := clockFree target (target.clock + extraClock)
  rw [copyRun] at clockedCopy
  simp only [Prod.map, id_eq] at clockedCopy
  have outputClock : {restored with clock := target.clock + extraClock} =
      {restored with clock := restored.clock + extraClock} := by rw [clockEq]
  rw [outputClock] at clockedCopy
  refine ⟨extraClock, bound, targetPost, targetResult, ?_, conclusion⟩
  rw [CallReturnEval.evaluateCopyRetSeq, StackSemEvaluate.evaluate_seq,
    StackSemEvaluateClock.fixClockEvaluate, clockedCopy]
  simp only
  exact continuationRun

theorem simulateReturningContinuationFromHistory (calleeBudget returnBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (ih : InductionHypotheses calleeBudget returnBudget ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost target (some (.result location returned)) (some (.result location)) (frame :: lens))
    (initial moved : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg width)
    (destination : Sum Nat Nat) (bodyExtraClock : Nat)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (destinationCompile : callDestNative dest args (k, callerSize, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, callerSize, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, callerSize, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock}) =
      (some (.result location), target)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F)
      (extraClock : Nat), extraClock ≤ returnBudget ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, target) = (none, restored) ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values returnCode,
          {target with clock := target.clock + extraClock}) = (targetResult, targetPost) ∧
      compCorrectResult ac k callerSize frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨popped, restored, popRun, sourceContinuation, continuationIH, copyRun, restoredRelation⟩ :=
    restoreCallerFromBodyReturn calleeBudget returnBudget ac k callerSize frame calleeSize calleeFrame values names
      retCode l1 l2 dest args source sourcePost bodyPost result location returned saved target
      lens xs args1 prog ss envs guards callerRelation conventions maximum ih nonzero
      execution notError bodyRun bodyConclusion
  obtain ⟨retConventions, retFlat, retMaximum, retLength, retBitmapBound, retBitmapPrefix, retLabels⟩ :=
    continuationCompilationFacts ac k callerSize frame values names retCode l1 l2 dest args
      initial bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
      returnCode compiled destination conventions flat maximum destinationCompile savedCompile
      returnCompile compilation lengthBound bitmapBound bitmapPrefix labels
  obtain ⟨bitmapGrowth, codeGrowth⟩ := returningHistoryGrowth initial saved moved target restored
    (.seq destinationCode savedCode)
    (stackArgsNative destination (args.length + 1) (k, callerSize, frame)) callee
    k callerSize frame l1 l2 bodyExtraClock values (some (.result location))
    preludeRun argumentsRun calleeRun copyRun
  have restoredLabels : ∀ loc, StackSem.getLabelsExact returnCode loc →
      StackSem.locCheckExact restored.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset initial.code restored.code codeGrowth loc (retLabels loc member)
  obtain ⟨extraClock, bound, targetPost, targetResult, targetContinuation, conclusion⟩ :=
    executeReturningContinuation calleeBudget returnBudget ac k callerSize frame values retCode
      (WordSemStateFiniteExact.setVars values returned popped) sourcePost target restored result
      savedBitmaps finalBitmaps savedIndex finalIndex returnCode lens continuationIH
      sourceContinuation notError restoredRelation retConventions retFlat returnCompile retLength
      (retBitmapBound.trans bitmapGrowth.length_le)
      (retBitmapPrefix.trans (bitmapGrowth.drop _)) restoredLabels retMaximum copyRun
  obtain ⟨gc, tail, sourceFrame, _, _, sourceHandler, _, _⟩ :=
    returnedCallerFrame prog source bodyPost envs args1 ss location returned bodyRun
  have poppedHandler : popped.handler = bodyPost.handler := by
    have pop := popRun
    rw [WordSemStateFiniteExact.popEnv, sourceFrame] at pop
    have shape := Option.some.inj pop
    rw [← shape]
  have handler : (WordSemStateFiniteExact.setVars values returned popped).handler = source.handler :=
    poppedHandler.trans sourceHandler
  rw [returningResultInitialHandler ac k callerSize frame source
    (WordSemStateFiniteExact.setVars values returned popped) sourcePost targetPost
    result targetResult lens handler] at conclusion
  exact ⟨popped, restored, extraClock, bound, targetPost, targetResult, popRun, copyRun,
    targetContinuation, conclusion⟩


#print axioms simulateReturningContinuationFromHistory
end InitECandidate.Runtime.WordToStack.CallReturning
