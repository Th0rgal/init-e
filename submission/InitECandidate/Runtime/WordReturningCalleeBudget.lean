import InitECandidate.Runtime.WordReturningBudgets
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning
namespace InitECandidate.Runtime.WordToStack.CallReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
theorem simulateCalleeBodyAt (calleeBudget returnBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
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
    (location calleeSize calleeFrame : Nat) (body : HolProg width)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (targetCode : sptLookup location saved.code = some
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body))
    (bodyCompile : compNative ac false prog (bs, n) (k, calleeSize, calleeFrame) =
      (body, (bsPost, nPost)))
    (bodyConventions : postAllocConventionsHOL k prog = true)
    (bodyFlat : flatExpConventions prog = true)
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ saved.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (saved.bitmaps.drop (n - (appListAppend bs).length)))
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (bodyMaximum : maxVarHOL prog < 2 * calleeFrame + 2 * k)
    (space : calleeSize ≤ saved.stackSpace) :
    ∃ (moved entry : StackSemStateFiniteExact width C F)
          (extraClock : Nat), extraClock ≤ calleeBudget ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost bodyResult targetResult (callerFrame :: lens) := by
  obtain ⟨moved, entry, moveRun, allocationRun, entryRelation⟩ :=
    enterCallee ac k callerSize callerFrame calleeSize calleeFrame values names retCode
      l1 l2 dest args source saved lens xs args1 prog ss envs destinationCode destination
      guards callerRelation pushedRelation conventions maximum destinationCompile
      calleeShape calleeLocalsSize argumentBound space
  have moveGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackArgsNative destination (args.length + 1) (k, callerSize, callerFrame))
    saved moved none moveRun
  have entryGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.stackAlloc (calleeSize - (args1.length - k)))
    (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved))
    entry none allocationRun
  have bitmapGrowth : saved.bitmaps.IsPrefix entry.bitmaps :=
    moveGrowth.1.trans entryGrowth.1
  have codeGrowth : sptSubspt saved.code entry.code :=
    sptSubsptTrans _ _ _ ⟨moveGrowth.2, entryGrowth.2⟩
  have labels : ∀ loc, StackSem.getLabelsExact body loc →
      StackSem.locCheckExact entry.code loc := by
    intro loc member
    apply LocationLabels.locCheckSubset saved.code entry.code codeGrowth loc
    exact Or.inr ⟨location, .seq (.stackAlloc (calleeSize - (args1.length - k))) body,
      targetCode, by unfold StackSem.getLabelsExact; exact Or.inr member⟩
  have bodyNotError := calleeNotError values names retCode l1 l2 dest args source
    sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution
    notError bodyRun
  obtain ⟨extraClock, clockBound, targetPost, targetResult, targetRun, conclusion⟩ :=
    ih.2 xs args1 prog ss envs ⟨guards, nonzero⟩ k calleeSize calleeFrame bodyPost entry
      bodyResult bs bsPost n nPost body (callerFrame :: lens)
      ⟨bodyRun, bodyNotError, entryRelation, bodyConventions, bodyFlat, bodyCompile,
        bitmapLength, bitmapBound.trans bitmapGrowth.length_le,
        bitmapPrefix.trans (bitmapGrowth.drop _), labels, bodyMaximum⟩
  have allocationClock : ∀ extra : Nat,
      StackSemEvaluate.evaluate
        (.stackAlloc (calleeSize - (args1.length - k)),
          {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
            clock := (StackSemStateOps.decClock moved).clock + extra}) =
        (none, {entry with clock := entry.clock + extra}) := by
    intro extra
    have success := allocationRun
    rw [StackSemEvaluate.evaluate_stackAlloc] at success
    split_ifs at success with disabled insufficient
    · cases (Prod.mk.inj success).1
    · cases (Prod.mk.inj success).1
    obtain ⟨_, rfl⟩ := Prod.mk.inj success
    rw [StackSemEvaluate.evaluate_stackAlloc, if_neg disabled, if_neg insufficient]
    rfl
  have calleeRun : StackSemEvaluate.evaluate
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
          clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
      (targetResult, targetPost) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      allocationClock extraClock]
    exact targetRun
  exact ⟨moved, entry, extraClock, clockBound, targetPost, targetResult, moveRun, allocationRun,
    targetRun, calleeRun, conclusion⟩


/-- Construct the actual returning-Call prelude and apply the original guarded
body IH to its SAME callee witness. No target evaluation or body result contract
is assumed: both are existential conclusions for every original body outcome.
The callee-capacity implication is the original allocation split; its failing
branch is handled separately by compiledCalleeFrameFailure. Untagged full-case infrastructure. -/
theorem simulatePreparedCalleeBody (calleeBudget returnBudget : Nat) {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
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
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤ target.stackSpace) :
    ∃ (destinationTarget saved moved : StackSemStateFiniteExact width C F)
      (location calleeSize calleeFrame : Nat) (body : HolProg width)
      (calleeBs calleeBsPost : AppList (BitVec width)) (calleeIndex calleeIndexPost : Nat),
      StackSemEvaluate.evaluate (destinationCode, target) = (none, destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode, destinationTarget) = (none, saved) ∧
      StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1) (k, f, frame), saved) =
        (none, moved) ∧
      stateRel ac k f frame source saved lens 0 ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
        saved (frame :: lens) 0 ∧
      sptLookup location source.code = some (args1.length, prog) ∧
      sptLookup location saved.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      compNative ac false prog (calleeBs, calleeIndex) (k, calleeSize, calleeFrame) =
        (body, (calleeBsPost, calleeIndexPost)) ∧
      postAllocConventionsHOL k prog = true ∧ flatExpConventions prog = true ∧
      (appListAppend calleeBs).length ≤ calleeIndex ∧
      calleeIndex - (appListAppend calleeBs).length ≤ target.bitmaps.length ∧
      (appListAppend calleeBsPost).IsPrefix
        (target.bitmaps.drop (calleeIndex - (appListAppend calleeBs).length)) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      args1.length - k ≤ calleeFrame ∧ maxVarHOL prog < 2 * calleeFrame + 2 * k ∧
      calleeFrame = max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code =
        some (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      saved.stackSpace = target.stackSpace ∧
      (calleeSize ≤ target.stackSpace →
        ∃ (entry : StackSemStateFiniteExact width C F) (extraClock : Nat), extraClock ≤ calleeBudget ∧ ∃
          (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost bodyResult targetResult (frame :: lens)) := by
  obtain ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, movedState⟩ :=
    prepareCalleeDestinationAt ac k f frame values names retCode l1 l2 dest args source target
      lens xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile bitmapLength bitmapBound
      bitmapPrefix space
  refine ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, ?_⟩
  intro calleeSpace
  have destinationGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    destinationCode target destinationTarget none destinationRun).1
  have savedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    savedCode destinationTarget saved none savedRun).1
  have bitmapGrowth : target.bitmaps.IsPrefix saved.bitmaps :=
    destinationGrowth.trans savedGrowth
  obtain ⟨movedAgain, entry, extraClock, clockBound, targetPost, targetResult, moveAgain,
    allocationRun, targetRun, calleeRun, conclusion⟩ :=
    simulateCalleeBodyAt calleeBudget returnBudget ac k f frame values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult saved lens xs args1 prog ss envs destinationCode destination
      guards savedRelation pushedRelation conventions maximum destinationCompile ih nonzero
      execution notError bodyRun location calleeSize calleeFrame body calleeBs calleeBsPost
      calleeIndex calleeIndexPost savedLookup bodyCompile bodyConventions bodyFlat
      calleeBitmapLength (calleeBitmapBound.trans bitmapGrowth.length_le)
      (calleeBitmapPrefix.trans (bitmapGrowth.drop _)) calleeLocalsSize calleeShape
      calleeArgumentBound bodyMaximum (by rwa [savedSpace])
  have movedEq : movedAgain = moved := congrArg Prod.snd (moveAgain.symm.trans moveRun)
  subst movedAgain
  exact ⟨entry, extraClock, clockBound, targetPost, targetResult, allocationRun, targetRun, calleeRun,
    conclusion⟩


#print axioms simulatePreparedCalleeBody
end InitECandidate.Runtime.WordToStack.CallReturning
