import InitECandidate.Runtime.WordStackReturningNormal
import InitECandidate.Runtime.StackReturningCallPropagateCost
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning.Execution
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- All callee outcomes after successful frame allocation, using only guarded
source induction hypotheses. Return work is absent for non-return outcomes. -/
theorem simulateSuccessfulCall (calleeBudget returnBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (bs savedBitmaps finalBitmaps : AppList (BitVec 64)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled : HolProg 64) (destination : Sum Nat Nat)
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
    (sourcePost bodyPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (result bodyResult : Option (WordSemResult 64))
    (ih : InductionHypothesesFor price calleeBudget returnBudget ac values names retCode l1 l2 dest args source)
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
      else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace)
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (frameSmall : f ≤ 92)
    (argsSmall : Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92)
    (returnsSmall : Flapjack.Compiler.Backend.WordToStack.numStackRet k values ≤ 92)
    (actualRegisters : k = 22) :
    ∃ (extra : Nat) (targetFinal : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (targetResult : Option (StackSemResult 64)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extra}) =
        (targetResult, targetFinal) ∧
      compCorrectResult ac k f frame source sourcePost targetFinal result targetResult lens ∧
      stackExecutionCost (fun p _ => price p) compiled
        {target with clock := target.clock+extra} ≤
      calleeBudget + 63 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k +
        (match (generalizing := false) bodyResult with
         | some (.result _ _) => returnBudget + 21 * Flapjack.Compiler.Backend.WordToStack.numStackRet k values
         | _ => 0) := by
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
    simulatePreparedCalleeBody (price := price) calleeBudget returnBudget ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile bitmapLength bitmapBound
      savedPrefix sourcePost bodyPost result bodyResult ih nonzero execution notError bodyRun argumentsSpace covered actualRegisters
  have calleeSpace : calleeSize ≤ target.stackSpace := by
    change calleeFrame = expectedFrame at calleeFrameEq
    change (if expectedFrame = 0 then 0 else expectedFrame + 1) ≤ _ at space
    rw [calleeFrameEq] at calleeShape
    split_ifs at calleeShape space <;> omega
  obtain ⟨entry, bodyExtra, calleeTarget, targetResult, allocationRun, bodyTargetRun,
    calleeRun, bodyConclusion, bodyCost, calleeCost⟩ := simulation calleeSpace
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
  have free := completePreludeClockFree (C := LabToTarget.Config) (F := F) k f frame dest args names
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
  let callee : HolProg 64 := .seq (.stackAlloc (calleeSize - (args1.length - k))) body
  let continuation : HolProg 64 := .seq .skip (copyRetNative false false (k, f, frame) values returnCode)
  have nonReturnCost (notReturn : ∀ value, targetResult ≠ some (.result value)) :
      stackExecutionCost (fun p _ => price p) compiled
        {target with clock := target.clock+bodyExtra} ≤
        calleeBudget + 63 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
    have callCost := stackCost_returning_call_propagate (price := price) callee continuation 0 l1 l2 destination moved calleeTarget
      targetResult bodyExtra (25+calleeBudget) movedNonzero found notReturn calleeRun calleeCost
    have bound := compiledCall_cost_from_prelude (price := price) ac k f frame values names retCode l1 l2 dest args
      bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
      target moved bodyExtra ((25+calleeBudget)+12)
      destinationCompile savedCompile returnCompile compilation frameSmall argsSmall preludeRun callCost
    omega
  have finishTerminal
      (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
        ∃ event, targetResult = some (.finalFFI event)) :
      ∃ extra targetFinal finalResult,
        StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extra}) =
          (finalResult, targetFinal) ∧
        compCorrectResult ac k f frame source sourcePost targetFinal result finalResult lens ∧
        stackExecutionCost (fun p _ => price p) compiled
          {target with clock := target.clock+extra} ≤
        calleeBudget + 63 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k +
          (match (generalizing := false) bodyResult with
           | some (.result _ _) => returnBudget + 21 * Flapjack.Compiler.Backend.WordToStack.numStackRet k values
           | _ => 0) := by
    obtain ⟨callRun, conclusion⟩ := terminalCallFromCallee ac k f frame calleeSize calleeFrame values
      names retCode l1 l2 dest args source sourcePost bodyPost result bodyResult target moved calleeTarget
      targetResult lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
      nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion terminal
    have cost := nonReturnCost (by
      intro value equal
      rcases terminal with timeout | ⟨value', halt⟩ | ⟨event, ffi⟩
      · rw [equal] at timeout
        cases timeout
      · rw [equal] at halt
        cases halt
      · rw [equal] at ffi
        cases ffi)
    exact ⟨bodyExtra, calleeTarget, targetResult,
      completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
        finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
        target moved calleeTarget bodyExtra targetResult destinationCompile savedCompile returnCompile
        compilation preludeRun callRun, conclusion, cost.trans (Nat.le_add_right _ _)⟩
  by_cases matching : bodyResult.map compileResult = targetResult
  · have outcomes := calleeOutcomeCases values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution bodyRun notError
    rcases outcomes with ⟨returnLocation, returned, rfl⟩ | ⟨exceptionLocation, value, rfl⟩ |
      timeout | resource | ⟨event, ffi⟩
    · have targetEq : targetResult = some (.result returnLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      obtain ⟨extra, final, output, run, conclusion, cost⟩ := normalCompiledCallFromHistory (price := price) calleeBudget returnBudget ac k f frame calleeSize calleeFrame values names retCode
        l1 l2 dest args source sourcePost bodyPost result returnLocation returned saved calleeTarget lens
        xs args1 prog ss envs guards savedRelation conventions maximum ih nonzero execution notError
        bodyRun bodyConclusion target moved bs savedBitmaps finalBitmaps n savedIndex finalIndex
        destinationCode savedCode returnCode compiled callee destination bodyExtra flat destinationCompile
        savedCompile returnCompile compilation bitmapLength bitmapBound bitmapPrefix labels savedPrelude
        argumentsRun calleeRun found frameSmall argsSmall returnsSmall calleeCost actualRegisters
      exact ⟨extra, final, output, run, conclusion, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cost⟩
    · have targetEq : targetResult = some (.exception exceptionLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      obtain ⟨callRun, conclusion⟩ := exceptionCallFromCallee ac k f frame calleeSize calleeFrame values
        names retCode l1 l2 dest args source sourcePost bodyPost result exceptionLocation value target moved
        calleeTarget lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
        nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion
      have cost := nonReturnCost (by intro candidate; change some (StackSemResult.exception exceptionLocation) ≠ some (.result candidate); intro equal; cases equal)
      exact ⟨bodyExtra, calleeTarget, some (.exception exceptionLocation),
        completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
          finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
          target moved calleeTarget bodyExtra (some (.exception exceptionLocation)) destinationCompile
          savedCompile returnCompile compilation preludeRun callRun, conclusion, by simpa only [Nat.add_zero] using cost⟩
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

#print axioms simulateSuccessfulCall
end InitECandidate.Runtime.WordToStack.ExecutedReturning
