import InitECandidate.Runtime.WordStackRegisteredSimulation
import InitECandidate.Runtime.WordStackReturningCallee
import InitECandidate.Runtime.WordStackReturningContinuation
import InitECandidate.Runtime.StackReturningCallComposeCost
import InitECandidate.Runtime.StackCostSeqAssoc
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning.Execution
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.StackToLab
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-! Normal returning-call composition from the actual callee history.
Setup pays 63 plus 39 per spilled argument and 21 per spilled return word;
callee and reached-continuation budgets add without a call-depth factor.
The enclosing all-outcome theorem separately handles failure/terminal cases. -/
theorem normalCompiledCallFromHistory (calleeBudget returnBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (result : Option (WordSemResult 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (saved target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
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
    (initial moved : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec 64)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg 64)
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
      (some (.result location), target))
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some callee)
    (frameSmall : callerSize ≤ 92)
    (argsSmall : Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92)
    (returnsSmall : Flapjack.Compiler.Backend.WordToStack.numStackRet k values ≤ 92)
    (calleeCost : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      callee {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock} ≤ 25+calleeBudget)
    (actualRegisters : k = 22) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (targetResult : Option (StackSemResult 64)),
      StackSemEvaluate.evaluate (compiled, {initial with clock := initial.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k callerSize frame source sourcePost targetPost result targetResult lens ∧
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) compiled
        {initial with clock := initial.clock + extraClock} ≤
      calleeBudget + returnBudget + 63 +
        39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k +
        21 * Flapjack.Compiler.Backend.WordToStack.numStackRet k values := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, valid, _, _⟩ := sourceReturningContinuation ac values names
    retCode l1 l2 dest args source sourcePost bodyPost result xs args1 prog ss envs location
    returned guards ih.forget nonzero execution notError bodyRun
  have locationEq : location = .loc l1 l2 := by
    by_contra different
    exact valid (Or.inl different)
  obtain ⟨popped, restored, continuationClock, finalTarget, finalResult, _, _, continuationRun,
    conclusion, continuationCost⟩ := simulateReturningContinuationFromHistory calleeBudget returnBudget ac k callerSize frame calleeSize
    calleeFrame values names retCode l1 l2 dest args source sourcePost bodyPost result location
    returned saved target lens xs args1 prog ss envs guards callerRelation conventions maximum
    ih nonzero execution notError bodyRun bodyConclusion initial moved bs savedBitmaps finalBitmaps
    n savedIndex finalIndex destinationCode savedCode returnCode compiled callee destination
    bodyExtraClock flat destinationCompile savedCompile returnCompile compilation lengthBound
    bitmapBound bitmapPrefix labels preludeRun argumentsRun calleeRun frameSmall returnsSmall actualRegisters
  have argumentClock := stackArgumentsClockFree (C := LabToTarget.Config) (F := F) k callerSize frame
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
  refine ⟨bodyExtraClock + continuationClock, finalTarget, finalResult, ?_, conclusion, ?_⟩
  · exact completeCallFromPrelude ac k callerSize frame values names retCode l1 l2 dest args
      bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled
      destination initial moved finalTarget (bodyExtraClock + continuationClock) finalResult
      destinationCompile savedCompile returnCompile compilation completePrelude callRun
  · let argsCode : HolProg 64 := stackArgsNative destination (args.length+1) (k,callerSize,frame)
    let returnSuffix : HolProg 64 := .seq .skip (copyRetNative false false (k,callerSize,frame) values returnCode)
    let callCode : HolProg 64 := .call (some (returnSuffix,0,l1,l2)) destination none
    let prelude : HolProg 64 := .seq destinationCode (.seq savedCode argsCode)
    have compiledEq : compiled = .seq destinationCode (.seq savedCode (.seq argsCode (.seq .skip callCode))) := by
      have shape := compilation
      simp only [compNative, destinationCompile, savedCompile, returnCompile] at shape
      simpa only [Bool.false_eq_true, ↓reduceIte] using (Prod.mk.inj shape).1.symm
    have prefixBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) prelude s ≤
          26 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
      intro s
      have destinationBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
          stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) destinationCode st ≤ 7 := by
        intro st
        have eq : (callDestNative dest args (k,callerSize,frame)).1 = destinationCode := congrArg Prod.fst destinationCompile
        rw [← eq]
        exact wordStack_callDest_cost dest args _ frameSmall st
      have saveBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
          stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) savedCode st ≤ 19 := by
        intro st
        have eq : (wLiveNative names (bs,n) (k,callerSize,frame)).1 = savedCode := congrArg Prod.fst savedCompile
        rw [← eq]
        exact wordStack_live_cost names (bs,n) (k,callerSize,frame) st
      have argumentsBound := wordStack_stackArgs_cost (F := F) destination (args.length+1)
        (k,callerSize,frame) frameSmall argsSmall
      have savedArgs : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
          stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (.seq savedCode argsCode) st ≤
          19 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
        intro st
        exact stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) savedCode argsCode
          19 _ rfl saveBound argumentsBound st
      have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) destinationCode
        (.seq savedCode argsCode) 7 _ rfl destinationBound savedArgs s
      change stackExecutionCost _ prelude s ≤ _ at bound
      omega
    have preludeShift := Compiler.Backend.StackProps.evaluateAddClock (bodyExtraClock+continuationClock)
      prelude initial none moved ⟨completePrelude, by simp⟩
    have reached := stackCost_seq_run prelude (.seq .skip callCode)
      {initial with clock := initial.clock + (bodyExtraClock+continuationClock)}
      {moved with clock := moved.clock + (bodyExtraClock+continuationClock)}
      (26 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k)
      preludeShift (prefixBound _)
    have suffixCost : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        returnSuffix {target with clock := target.clock + continuationClock} ≤
        21 * Flapjack.Compiler.Backend.WordToStack.numStackRet k values + returnBudget := by
      dsimp only [returnSuffix]
      rw [stackExecutionCost_seq]
      simpa only [show removalLocalPrice 6 riscvConfig.addrOffset
          (.seq .skip (copyRetNative false false (k,callerSize,frame) values returnCode)) = 0 from rfl,
        stackExecutionCost, show removalLocalPrice 6 riscvConfig.addrOffset .skip = 0 from rfl,
        Nat.zero_add, StackSemEvaluate.evaluate_skip] using continuationCost
    have callCost := stackCost_returning_call_compose callee returnSuffix 0 l1 l2 destination moved target
      bodyExtraClock continuationClock (25+calleeBudget)
      (21 * Flapjack.Compiler.Backend.WordToStack.numStackRet k values + returnBudget)
      movedNonzero found calleeRun calleeCost suffixCost
    have reassoc : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        compiled {initial with clock := initial.clock + (bodyExtraClock+continuationClock)} =
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
          (.seq prelude (.seq .skip callCode)) {initial with clock := initial.clock + (bodyExtraClock+continuationClock)} := by
      rw [compiledEq]
      dsimp only [prelude]
      rw [stackCost_seq_assoc]
      exact stackCost_seq_congr_right destinationCode _ _
        (fun st => (stackCost_seq_assoc savedCode argsCode (.seq .skip callCode) st).symm) _
    rw [reassoc]
    have skipCall : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.seq .skip callCode) {moved with clock := moved.clock + (bodyExtraClock+continuationClock)} =
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        callCode {moved with clock := moved.clock + (bodyExtraClock+continuationClock)} := by
      rw [stackExecutionCost_seq]
      simp only [show removalLocalPrice 6 riscvConfig.addrOffset (.seq .skip callCode) = 0 from rfl,
        stackExecutionCost, show removalLocalPrice 6 riscvConfig.addrOffset .skip = 0 from rfl,
        StackSemEvaluate.evaluate_skip, Nat.zero_add]
    rw [skipCall] at reached
    change stackExecutionCost _ (.seq prelude (.seq .skip callCode)) _ ≤ _
    change stackExecutionCost _ callCode _ ≤ _ at callCost
    omega

#print axioms normalCompiledCallFromHistory
end InitECandidate.Runtime.WordToStack.ExecutedReturning
