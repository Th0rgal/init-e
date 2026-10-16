import InitECandidate.Runtime.WordReturningCalleeBudget
import InitECandidate.Runtime.WordReturningContinuationBudget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning.Execution
namespace InitECandidate.Runtime.WordToStack.CallReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-! Bounded all-outcome returning Call without an installed exception handler.
Actual callee and reached continuation budgets add; zero-fuel and allocation
failures retain their zero witnesses and full resource/trace conclusions. -/
theorem normalCompiledCallFromHistory (calleeBudget returnBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
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
    (bodyBound : bodyExtraClock ≤ calleeBudget)
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
      (some (.result location), target))
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some callee) :
    ∃ (extraClock : Nat), extraClock ≤ calleeBudget + returnBudget ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {initial with clock := initial.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k callerSize frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, valid, _, _⟩ := sourceReturningContinuation ac values names
    retCode l1 l2 dest args source sourcePost bodyPost result xs args1 prog ss envs location
    returned guards ih.forget nonzero execution notError bodyRun
  have locationEq : location = .loc l1 l2 := by
    by_contra different
    exact valid (Or.inl different)
  obtain ⟨popped, restored, continuationClock, returnBound, finalTarget, finalResult, _, _, continuationRun,
    conclusion⟩ := simulateReturningContinuationFromHistory calleeBudget returnBudget ac k callerSize frame calleeSize
    calleeFrame values names retCode l1 l2 dest args source sourcePost bodyPost result location
    returned saved target lens xs args1 prog ss envs guards callerRelation conventions maximum
    ih nonzero execution notError bodyRun bodyConclusion initial moved bs savedBitmaps finalBitmaps
    n savedIndex finalIndex destinationCode savedCode returnCode compiled callee destination
    bodyExtraClock flat destinationCompile savedCompile returnCompile compilation lengthBound
    bitmapBound bitmapPrefix labels preludeRun argumentsRun calleeRun
  have argumentClock := stackArgumentsClockFree (C := C) (F := F) k callerSize frame
    destination (args.length + 1) saved saved.clock
  change StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) =
    Prod.map id (fun state => {state with clock := saved.clock})
      (StackSemEvaluate.evaluate
        (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved)) at argumentClock
  rw [argumentsRun] at argumentClock
  have movedClock : moved.clock = saved.clock :=
    congrArg (fun state => state.clock) (Prod.mk.inj argumentClock).2
  have movedNonzero : moved.clock ≠ 0 := by
    rw [movedClock, ← callerRelation.1]
    exact nonzero
  have actualContinuation : StackSemEvaluate.evaluate
      (.seq .skip (copyRetNative false false (k, callerSize, frame) values returnCode),
        {target with clock := target.clock + continuationClock}) = (finalResult, finalTarget) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_skip]
    exact continuationRun
  rw [locationEq] at calleeRun
  have callRun := returningCallContinuationRun moved target finalTarget l1 l2 bodyExtraClock
    continuationClock destination callee
    (.seq .skip (copyRetNative false false (k, callerSize, frame) values returnCode)) finalResult
    found movedNonzero calleeRun actualContinuation
  have completePrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode
        (stackArgsNative destination (args.length + 1) (k, callerSize, frame))), initial) =
      (none, moved) := by
    rw [Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
      StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, preludeRun]
    exact argumentsRun
  refine ⟨bodyExtraClock + continuationClock, Nat.add_le_add bodyBound returnBound, finalTarget, finalResult, ?_, conclusion⟩
  exact completeCallFromPrelude ac k callerSize frame values names retCode l1 l2 dest args
    bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled
    destination initial moved finalTarget (bodyExtraClock + continuationClock) finalResult
    destinationCompile savedCompile returnCompile compilation completePrelude callRun

/-- Assemble every callee outcome of the original successful NONE returning
Call allocation branch. Actual setup and the original guarded body IH construct
the callee execution and complete result/resource contract internally. The
original continuation IH supplies normal return execution; exceptions and all
terminal/mismatch outcomes use the actual native Call clauses. No target run or
callee contract is assumed. Untagged original-case assembly pending final
zero-clock/allocation-failure composition and source review. -/
theorem simulateSuccessfulCall (calleeBudget returnBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, f, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (ih : InductionHypotheses calleeBudget returnBudget ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (space : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace) :
    ∃ (extra : Nat), extra ≤ calleeBudget + returnBudget ∧ ∃ (targetFinal : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extra}) =
        (targetResult, targetFinal) ∧
      compCorrectResult ac k f frame source sourcePost targetFinal result targetResult lens := by
  let expectedFrame := max (maxVarHOL prog / 2 + 1 - k) (args1.length - k)
  have countEq := stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k f frame destinationCode destination guards destinationCompile
  have argumentsSpace : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace := by
    rw [countEq]
    have bound : args1.length - k ≤ expectedFrame := Nat.le_max_right _ _
    change (if expectedFrame = 0 then 0 else expectedFrame + 1) ≤ _ at space
    split_ifs at space <;> omega
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps, savedIndex) (k, f, frame)
    returnCode (finalBitmaps, finalIndex) returnCompile).trans bitmapPrefix
  obtain ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, argumentsRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, simulation⟩ :=
    simulatePreparedCalleeBody calleeBudget returnBudget ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile bitmapLength bitmapBound
      savedPrefix sourcePost bodyPost result bodyResult ih nonzero execution notError bodyRun argumentsSpace
  have calleeSpace : calleeSize ≤ target.stackSpace := by
    change calleeFrame = expectedFrame at calleeFrameEq
    change (if expectedFrame = 0 then 0 else expectedFrame + 1) ≤ _ at space
    rw [calleeFrameEq] at calleeShape
    split_ifs at calleeShape space <;> omega
  obtain ⟨entry, bodyExtra, bodyBound, calleeTarget, targetResult, allocationRun, bodyTargetRun,
    calleeRun, bodyConclusion⟩ := simulation calleeSpace
  have savedPrelude : StackSemEvaluate.evaluate (.seq destinationCode savedCode, target) =
      (none, saved) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    exact savedRun
  have preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode
        (stackArgsNative destination (args.length + 1) (k, f, frame))), target) = (none, moved) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    exact argumentsRun
  have free := completePreludeClockFree (C := C) (F := F) k f frame dest args names
    (bs, n) (savedBitmaps, savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free target target.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode
      (stackArgsNative destination (args.length + 1) (k, f, frame))), target) =
    (Prod.map id (fun state => {state with clock := target.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode
          (stackArgsNative destination (args.length + 1) (k, f, frame))), target)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = target.clock := congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by rw [clockEq, ← related.1]; exact nonzero
  let callee : HolProg width := .seq (.stackAlloc (calleeSize - (args1.length - k))) body
  let continuation : HolProg width := .seq .skip (copyRetNative false false (k, f, frame) values returnCode)
  have finishTerminal
      (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
        ∃ event, targetResult = some (.finalFFI event)) :
      ∃ extra, extra ≤ calleeBudget + returnBudget ∧ ∃ targetFinal finalResult,
        StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extra}) =
          (finalResult, targetFinal) ∧
        compCorrectResult ac k f frame source sourcePost targetFinal result finalResult lens := by
    obtain ⟨callRun, conclusion⟩ := terminalCallFromCallee ac k f frame calleeSize calleeFrame values
      names retCode l1 l2 dest args source sourcePost bodyPost result bodyResult target moved calleeTarget
      targetResult lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
      nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion terminal
    exact ⟨bodyExtra, by omega, calleeTarget, targetResult,
      completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
        finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
        target moved calleeTarget bodyExtra targetResult destinationCompile savedCompile returnCompile
        compilation preludeRun callRun, conclusion⟩
  by_cases matching : bodyResult.map compileResult = targetResult
  · have outcomes := calleeOutcomeCases values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution bodyRun notError
    rcases outcomes with ⟨returnLocation, returned, rfl⟩ | ⟨exceptionLocation, value, rfl⟩ |
      timeout | resource | ⟨event, ffi⟩
    · have targetEq : targetResult = some (.result returnLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      exact normalCompiledCallFromHistory calleeBudget returnBudget ac k f frame calleeSize calleeFrame values names retCode
        l1 l2 dest args source sourcePost bodyPost result returnLocation returned saved calleeTarget lens
        xs args1 prog ss envs guards savedRelation conventions maximum ih nonzero execution notError
        bodyRun bodyConclusion target moved bs savedBitmaps finalBitmaps n savedIndex finalIndex
        destinationCode savedCode returnCode compiled callee destination bodyExtra bodyBound flat destinationCompile
        savedCompile returnCompile compilation bitmapLength bitmapBound bitmapPrefix labels savedPrelude
        argumentsRun calleeRun found
    · have targetEq : targetResult = some (.exception exceptionLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      obtain ⟨callRun, conclusion⟩ := exceptionCallFromCallee ac k f frame calleeSize calleeFrame values
        names retCode l1 l2 dest args source sourcePost bodyPost result exceptionLocation value target moved
        calleeTarget lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
        nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion
      exact ⟨bodyExtra, by omega, calleeTarget, some (.exception exceptionLocation),
        completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
          finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
          target moved calleeTarget bodyExtra (some (.exception exceptionLocation)) destinationCompile
          savedCompile returnCompile compilation preludeRun callRun, conclusion⟩
    · apply finishTerminal; left
      simpa only [timeout, Option.map_some, compileResult] using matching.symm
    · apply finishTerminal; right; left
      exact ⟨.word 1, by simpa only [resource, Option.map_some, compileResult] using matching.symm⟩
    · apply finishTerminal; right; right
      exact ⟨event, by simpa only [ffi, Option.map_some, compileResult] using matching.symm⟩
  · have mismatch := bodyConclusion
    unfold compCorrectResult at mismatch
    rw [if_pos matching] at mismatch
    exact finishTerminal (Or.inr (Or.inl ⟨.word 2, mismatch.1⟩))

theorem compCorrectCallReturningNone (calleeBudget returnBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : InductionHypotheses calleeBudget returnBudget ac values names retCode l1 l2 dest args source) :
    BoundedSimulation ac (.call (some (values, names, retCode, l1, l2)) dest args none) source
      (calleeBudget + returnBudget) := by
  intro k f frame sourcePost target result bs finalBitmaps n finalIndex compiled lens premises
  obtain ⟨execution, notError, related, conventions, flat, compilation, bitmapLength,
    bitmapBound, bitmapPrefix, labels, maximum⟩ := premises
  obtain ⟨xs, args1, prog, ss, envs, guards⟩ := sourceGuardsOfNotError values names retCode l1 l2
    dest args source sourcePost result execution notError
  rcases destinationCompile : callDestNative (width := width) dest args (k, f, frame) with ⟨destinationCode, destination⟩
  rcases savedCompile : wLiveNative names (bs, n) (k, f, frame) with
    ⟨savedCode, savedBitmaps, savedIndex⟩
  rcases returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) with
    ⟨returnCode, returnBitmaps, returnIndex⟩
  have shape := compilation
  simp only [compNative, destinationCompile, savedCompile, returnCompile,
    Bool.false_eq_true, if_false, Prod.mk.injEq] at shape
  obtain ⟨bitmapsEq, indexEq⟩ := shape.2
  subst finalBitmaps
  subst finalIndex
  by_cases argumentsSpace : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace
  · by_cases zero : source.clock = 0
    · obtain ⟨targetPost, run, conclusion⟩ := compiledCallTimeout ac k f frame values names retCode
        l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
        returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards
        related conventions maximum destinationCompile savedCompile returnCompile bitmapLength
        bitmapBound compiled compilation execution argumentsSpace zero bitmapPrefix
      exact ⟨0, Nat.zero_le _, targetPost, some .timeOut, by simpa only [Nat.add_zero] using run, conclusion⟩
    · by_cases calleeSpace : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
          else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace
      · rcases bodyRun : WordSemStateFiniteExact.evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) with
          ⟨bodyResult, bodyPost⟩
        exact simulateSuccessfulCall calleeBudget returnBudget ac k f frame values names retCode l1 l2 dest args source target
          lens xs args1 prog ss envs bs savedBitmaps returnBitmaps n savedIndex returnIndex
          destinationCode savedCode returnCode compiled destination guards related conventions maximum
          destinationCompile savedCompile returnCompile compilation flat labels bitmapLength bitmapBound
          bitmapPrefix sourcePost bodyPost result bodyResult ih zero execution notError bodyRun calleeSpace
      · obtain ⟨calleeSize, _, sizeEq, failure⟩ := compiledCalleeFrameFailure ac k f frame values names
          retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
          returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards
          related conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound
          compiled compilation execution argumentsSpace zero bitmapPrefix
        obtain ⟨targetPost, run, conclusion⟩ := failure (by rw [sizeEq]; omega)
        exact ⟨0, Nat.zero_le _, targetPost, some (.halt (.word (BitVec.ofNat width 2))), by simpa only [Nat.add_zero] using run, conclusion⟩
  · obtain ⟨targetPost, run, conclusion⟩ := compiledStackArgumentsFailure ac k f frame values names
      retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
      returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards related
      conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound compiled
      compilation execution (by omega) bitmapPrefix
    exact ⟨0, Nat.zero_le _, targetPost, some (.halt (.word (BitVec.ofNat width 2))), by simpa only [Nat.add_zero] using run, conclusion⟩


#print axioms compCorrectCallReturningNone
end InitECandidate.Runtime.WordToStack.CallReturning
