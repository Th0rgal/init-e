import InitECandidate.Runtime.WordStackReturningMotive
import InitECandidate.Runtime.StackCallRunCost
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend
open InitECandidate.Runtime.StackToLab
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
theorem simulateCalleeBodyAt (calleeBudget returnBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (result bodyResult : Option (WordSemResult 64))
    (saved : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (destinationCode : HolProg 64) (destination : Sum Nat Nat)
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
    (location calleeSize calleeFrame : Nat) (body : HolProg 64)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
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
    (space : calleeSize ≤ saved.stackSpace)
    (calleeSmall : calleeSize ≤ 92) :
    ∃ (moved entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
          (extraClock : Nat) (targetPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
          (targetResult : Option (StackSemResult 64)),
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
            bodyPost targetPost bodyResult targetResult (callerFrame :: lens) ∧
          stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
            body {entry with clock := entry.clock + extraClock} ≤ calleeBudget ∧
          stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body)
            {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
              clock := (StackSemStateOps.decClock moved).clock + extraClock} ≤ 25 + calleeBudget := by
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
  obtain ⟨extraClock, targetPost, targetResult, targetRun, conclusion, bodyCost⟩ :=
    ih.2 xs args1 prog ss envs ⟨guards, nonzero⟩ k calleeSize calleeFrame bodyPost entry
      bodyResult bs bsPost n nPost body (callerFrame :: lens)
      ⟨bodyRun, bodyNotError, entryRelation, bodyConventions, bodyFlat, bodyCompile,
        bitmapLength, bitmapBound.trans bitmapGrowth.length_le,
        bitmapPrefix.trans (bitmapGrowth.drop _), labels, bodyMaximum⟩ calleeSmall
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
  refine ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    targetRun, calleeRun, conclusion, bodyCost, ?_⟩
  have bound := stackCost_seq_run (.stackAlloc (calleeSize - (args1.length - k))) body
    _ _ 25 (allocationClock extraClock)
    (by simpa only [stackExecutionCost] using guest_frame_alloc_price (calleeSize - (args1.length - k)) (by omega))
  exact bound.trans (Nat.add_le_add_left bodyCost 25)

#print axioms simulateCalleeBodyAt
end InitECandidate.Runtime.WordToStack.ExecutedReturning
