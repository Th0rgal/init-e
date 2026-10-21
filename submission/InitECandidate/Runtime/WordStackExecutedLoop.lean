import InitECandidate.Runtime.WordStackExecutedSimulation
import InitECandidate.Runtime.StackExecutionCostAddClock
import InitECandidate.Runtime.StackRemoveExecutedLoop
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Loop
namespace InitECandidate.Runtime.WordToStack.ExecutedLoop
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.StackToLab
open Flapjack.WordToStackProofs.CompCorrect.Loop
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-! Additive bounded Loop composition using only its actual cut/body run and
continuing nonzero-clock reentry. All original resource-limit branches remain. -/
def InductionHypotheses (bodyBudget recursiveBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) : Prop :=
  (∀ cutSource bodyResult bodyPost,
    WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource ∧
    (bodyResult,bodyPost) = WordSemStateFiniteExact.evaluate body cutSource ∧
    wordSemContLoop bodyResult = true ∧ bodyPost.clock ≠ 0 →
    ExecutedSimulation ac (wordSemSTOP (.loop names body exitNames))
      (WordSemStateFiniteExact.decClock bodyPost) recursiveBudget) ∧
  (∀ cutSource, WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource →
    ExecutedSimulation ac body cutSource bodyBudget)

theorem enterBody (bodyBudget recursiveBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec 64))
    (source cutSource bodyPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (k f frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : Compiler.Backend.StackLang.HolProg 64) (bodyResult : Option (WordSemResult 64))
    (ih : InductionHypotheses bodyBudget recursiveBudget ac names exitNames body source)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (execution : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (notError : bodyResult ≠ some .error)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k (.loop names body exitNames) = true)
    (flat : flatExpConventions (.loop names body exitNames) = true)
    (compilation : compNative ac false (.loop names body exitNames) (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (maxBound : maxVarHOL (.loop names body exitNames) < 2*frame+2*k)
    (small : f ≤ 92) :
    ∃ compiledBody ck targetPost targetResult,
      compiled = .loop compiledBody ∧
      StackSemEvaluate.evaluate (compiledBody,{target with clock := target.clock+ck}) = (targetResult,targetPost) ∧
      compCorrectResult ac k f frame cutSource bodyPost targetPost bodyResult targetResult lens ∧
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        compiledBody {target with clock := target.clock+ck} ≤ bodyBudget := by
  rcases bodyComp : compNative ac false body (bs,n) (k,f,frame) with ⟨compiledBody,next⟩
  simp only [compNative,bodyComp,Prod.mk.injEq] at compilation
  obtain ⟨rfl,nextEq⟩ := compilation
  have cutRel := StateRelCutState.stateRelCutState ac k f frame source cutSource target lens names related cut
  have bodyConventions : postAllocConventionsHOL k body = true := by
    simp [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,callArgConventionHOL] at conventions ⊢
    exact ⟨conventions.1.1.2,conventions.2⟩
  have bodyFlat : flatExpConventions body = true := by simpa [flatExpConventions] using flat
  have bodyBound : maxVarHOL body < 2*frame+2*k := by
    simp only [maxVarHOL,max3HOL] at maxBound
    split at maxBound <;> split at maxBound <;> omega
  have bodyLabels : ∀ loc, StackSem.getLabelsExact compiledBody loc → StackSem.locCheckExact target.code loc := by
    simpa [StackSem.getLabelsExact] using labels
  have compilationBody : compNative ac false body (bs,n) (k,f,frame) = (compiledBody,(bsPost,nPost)) := by
    simpa [nextEq] using bodyComp
  obtain ⟨ck,post,res,actual,resultRel,cost⟩ := ih.2 cutSource cut k f frame bodyPost target
    bodyResult bs bsPost n nPost compiledBody lens
    ⟨execution,notError,cutRel,bodyConventions,bodyFlat,compilationBody,
      lengthBound,bitmapBound,bitmapPrefix,bodyLabels,bodyBound⟩ small
  exact ⟨compiledBody,ck,post,res,rfl,actual,resultRel,cost⟩

theorem enterRecursive (bodyBudget recursiveBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec 64))
    (source cutSource bodyPost finalSource : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (target targetBody : StackSemStateFiniteExact 64 LabToTarget.Config F) (k f frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost bodyClock : Nat)
    (compiledBody : Compiler.Backend.StackLang.HolProg 64)
    (bodyResult finalResult : Option (WordSemResult 64))
    (ih : InductionHypotheses bodyBudget recursiveBudget ac names exitNames body source)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (sourceBody : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (continues : wordSemContLoop bodyResult = true) (nonzero : bodyPost.clock ≠ 0)
    (sourceRecursive : WordSemStateFiniteExact.evaluate (.loop names body exitNames)
      (WordSemStateFiniteExact.decClock bodyPost) = (finalResult,finalSource))
    (notError : finalResult ≠ some .error)
    (targetRun : StackSemEvaluate.evaluate (compiledBody,{target with clock := target.clock+bodyClock}) =
      (bodyResult.map compileResult,targetBody))
    (bodyConclusion : compCorrectResult ac k f frame cutSource bodyPost targetBody
      bodyResult (bodyResult.map compileResult) lens)
    (conventions : postAllocConventionsHOL k (.loop names body exitNames) = true)
    (flat : flatExpConventions (.loop names body exitNames) = true)
    (compilation : compNative ac false (.loop names body exitNames) (bs,n) (k,f,frame) =
      (.loop compiledBody,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact (.loop compiledBody) loc → StackSem.locCheckExact target.code loc)
    (maxBound : maxVarHOL (.loop names body exitNames) < 2*frame+2*k)
    (small : f ≤ 92) :
    ∃ clock targetPost result,
      StackSemEvaluate.evaluate (.loop compiledBody,
        {StackSemStateOps.decClock targetBody with clock := (StackSemStateOps.decClock targetBody).clock+clock}) =
        (result,targetPost) ∧
      compCorrectResult ac k f frame (WordSemStateFiniteExact.decClock bodyPost)
        finalSource targetPost finalResult result lens ∧
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.loop compiledBody) {StackSemStateOps.decClock targetBody with clock :=
          (StackSemStateOps.decClock targetBody).clock+clock} ≤ recursiveBudget := by
  have recursiveIH := ih.1 cutSource bodyResult bodyPost ⟨cut,sourceBody.symm,continues,nonzero⟩
  have metadata := recursiveMetadata compiledBody target targetBody (bodyResult.map compileResult)
    bodyClock (n-(appListAppend bs).length) (appListAppend bsPost) targetRun bitmapBound bitmapPrefix labels
  have relation := recursiveRelation ac k f frame cutSource bodyPost targetBody lens bodyResult continues bodyConclusion
  apply recursiveIH k f frame finalSource (StackSemStateOps.decClock targetBody)
    finalResult bs bsPost n nPost (.loop compiledBody) lens ?_ small
  simpa only [wordSemSTOP,StackSemStateOps.decClock] using
    (show WordSemStateFiniteExact.evaluate (.loop names body exitNames)
      (WordSemStateFiniteExact.decClock bodyPost) = (finalResult,finalSource) ∧
      finalResult ≠ some .error ∧ stateRel ac k f frame
        (WordSemStateFiniteExact.decClock bodyPost) (StackSemStateOps.decClock targetBody) lens 0 ∧
      postAllocConventionsHOL k (.loop names body exitNames) = true ∧
      flatExpConventions (.loop names body exitNames) = true ∧
      compNative ac false (.loop names body exitNames) (bs,n) (k,f,frame) = (.loop compiledBody,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ targetBody.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (targetBody.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc,StackSem.getLabelsExact (.loop compiledBody) loc → StackSem.locCheckExact targetBody.code loc) ∧
      maxVarHOL (.loop names body exitNames) < 2*frame+2*k from
      ⟨sourceRecursive,notError,relation,conventions,flat,compilation,lengthBound,
        metadata.1,metadata.2.1,metadata.2.2,maxBound⟩)

theorem compCorrectLoop (bodyBudget recursiveBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ih : InductionHypotheses bodyBudget recursiveBudget ac names exitNames body source) :
    ExecutedSimulation ac (.loop names body exitNames) source (2 + bodyBudget + recursiveBudget) := by
  classical
  intro k f frame finalSource target finalResult bs bsPost n nPost compiled lens premises small
  rcases premises with ⟨sourceLoop,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  cases cut : WordSemStateFiniteExact.cutState (names,.ln) source with
  | none =>
    rw [WordSemStateFiniteExact.evaluate,cut] at sourceLoop
    have error : finalResult = some .error := congrArg Prod.fst sourceLoop.symm
    exact False.elim (notError error)
  | some cutSource =>
    rcases sourceBody : WordSemStateFiniteExact.evaluate body cutSource with ⟨bodyResult,bodyPost⟩
    have bodyError := bodyNonError names exitNames body source cutSource bodyPost finalSource
      bodyResult finalResult cut sourceBody sourceLoop notError
    obtain ⟨compiledBody,bodyClock,targetBody,targetResult,compiledEq,targetRun,bodyConclusion,bodyCost⟩ :=
      enterBody bodyBudget recursiveBudget ac names exitNames body source cutSource bodyPost target k f frame lens
        bs bsPost n nPost compiled bodyResult ih cut sourceBody bodyError related conventions
        flat compilation lengthBound bitmapBound bitmapPrefix labels maxBound small
    subst compiled
    by_cases mismatch : bodyResult.map compileResult ≠ targetResult
    · have overflow := bodyOverflow ac k f frame names exitNames body source cutSource bodyPost
        finalSource target targetBody lens compiledBody bodyClock bodyResult finalResult targetResult
        related cut sourceBody sourceLoop targetRun bodyConclusion mismatch
      refine ⟨bodyClock,targetBody,some (.halt (.word 2)),overflow.1,overflow.2,?_⟩
      have resultHalt : targetResult = some (.halt (.word 2)) := by
        have overflowRel := bodyConclusion
        unfold compCorrectResult at overflowRel
        split at overflowRel
        · exact overflowRel.1
        · rename_i equal
          exact False.elim (mismatch (by simpa using equal))
      rw [stackExecutionCost_loop_run _ _ _ _ _ targetRun]
      simp only [resultHalt, StackSemControl.contLoop, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      change 2 + _ ≤ 2 + bodyBudget + recursiveBudget
      omega
    · have resultEq : targetResult = bodyResult.map compileResult := (not_ne_iff.mp mismatch).symm
      subst targetResult
      have tailRun := sourceLoop
      rw [WordSemStateFiniteExact.evaluate,cut] at tailRun
      simp only [] at tailRun
      rw [WordSemStateFiniteExact.fix_clock_evaluate,sourceBody] at tailRun
      by_cases continues : wordSemContLoop bodyResult = true
      · have bodyRel := continuationRelation ac k f frame cutSource bodyPost targetBody lens
          bodyResult continues bodyConclusion
        have clocks := bodyRel.1
        have targetContinues : StackSemControl.contLoop (bodyResult.map compileResult) = true := by
          rw [contLoopCompile,continues]
        simp only [continues] at tailRun
        by_cases zero : bodyPost.clock = 0
        · simp only [zero] at tailRun
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj tailRun
          have targetZero : targetBody.clock = 0 := by omega
          refine ⟨bodyClock,StackSemStateOps.emptyEnv targetBody,some .timeOut,
            runLoopTimeout compiledBody {target with clock := target.clock+bodyClock} targetBody
              (bodyResult.map compileResult) targetRun targetContinues targetZero,
            timeoutRelation ac k f frame source bodyPost targetBody lens bodyRel, ?_⟩
          rw [stackExecutionCost_loop_run _ _ _ _ _ targetRun]
          simp only [targetZero, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          change 2 + _ ≤ 2 + bodyBudget + recursiveBudget
          omega
        · simp only [zero] at tailRun
          obtain ⟨recursiveClock,post,res,recursiveRun,recursiveConclusion,recursiveCost⟩ :=
            enterRecursive bodyBudget recursiveBudget ac names exitNames body source cutSource bodyPost finalSource target targetBody
              k f frame lens bs bsPost n nPost bodyClock compiledBody bodyResult finalResult ih cut sourceBody
              continues zero (by simpa [wordSemSTOP] using tailRun) notError targetRun bodyConclusion
              conventions flat compilation lengthBound bitmapBound bitmapPrefix labels maxBound small
          have targetNonzero : targetBody.clock ≠ 0 := by omega
          have actual := runLoopRecursive compiledBody {target with clock := target.clock+bodyClock}
            targetBody post (bodyResult.map compileResult) res recursiveClock targetRun targetContinues
            targetNonzero recursiveRun
          have sourceHandler : source.handler = (WordSemStateFiniteExact.decClock bodyPost).handler := by
            have bodyHandler := LoopHandler.evaluateContLoopHandler body cutSource bodyPost bodyResult sourceBody continues
            have initialHandler := cutHandler names source cutSource cut
            simpa [WordSemStateFiniteExact.decClock] using initialHandler.trans bodyHandler.symm
          refine ⟨bodyClock+recursiveClock,post,res,?_,?_,?_⟩
          · simpa [Nat.add_assoc] using actual
          · exact originRelation ac k f frame source (WordSemStateFiniteExact.decClock bodyPost)
              finalSource post lens finalResult res sourceHandler recursiveConclusion
          · have notTimeout : bodyResult.map compileResult ≠ some .timeOut := by
              intro equal
              rw [equal] at targetContinues
              simp [StackSemControl.contLoop] at targetContinues
            have boosted := Flapjack.Compiler.Backend.StackProps.evaluateAddClock
              recursiveClock compiledBody {target with clock := target.clock+bodyClock}
              (bodyResult.map compileResult) targetBody ⟨targetRun, notTimeout⟩
            have startEq : {target with clock := target.clock+(bodyClock+recursiveClock)} =
                {{target with clock := target.clock+bodyClock} with clock :=
                  (target.clock+bodyClock)+recursiveClock} := by simp only [Nat.add_assoc]
            have bodyStable := stackExecutionCost_addClock
              (removalLocalPrice 6 riscvConfig.addrOffset) compiledBody
              {target with clock := target.clock+bodyClock} targetBody
              (bodyResult.map compileResult) targetRun notTimeout recursiveClock
            rw [startEq, stackExecutionCost_loop_run _ _ _ _ _ boosted]
            have boostedNonzero : ({targetBody with clock := targetBody.clock+recursiveClock}).clock ≠ 0 := by
              change targetBody.clock+recursiveClock ≠ 0
              omega
            simp only [targetContinues, boostedNonzero, bne_iff_ne, Bool.true_and, if_pos boostedNonzero]
            have decEq : StackSemStateOps.decClock {targetBody with clock := targetBody.clock+recursiveClock} =
                {StackSemStateOps.decClock targetBody with clock :=
                  (StackSemStateOps.decClock targetBody).clock+recursiveClock} := by
              change {targetBody with clock := targetBody.clock+recursiveClock-1} =
                {targetBody with clock := (targetBody.clock-1)+recursiveClock}
              have arithmetic : targetBody.clock+recursiveClock-1 = (targetBody.clock-1)+recursiveClock := by omega
              rw [arithmetic]
            rw [decEq, bodyStable]
            change 2 + _ + _ ≤ 2 + bodyBudget + recursiveBudget
            exact Nat.add_le_add (Nat.add_le_add_left bodyCost 2) recursiveCost
      · simp only [continues] at tailRun
        by_cases breakZero : bodyResult = some (.break 0)
        · subst bodyResult
          cases exitCut : WordSemStateFiniteExact.cutState (exitNames,.ln) bodyPost with
          | none =>
            simp [exitCut] at tailRun
            obtain ⟨rfl,rfl⟩ := tailRun
            contradiction
          | some exitPost =>
            simp [exitCut] at tailRun
            obtain ⟨rfl,rfl⟩ := tailRun
            refine ⟨bodyClock,targetBody,none,
              runLoopBreakZero compiledBody {target with clock := target.clock+bodyClock} targetBody targetRun,
              breakZeroRelation ac k f frame source cutSource bodyPost exitPost targetBody lens exitNames
                bodyConclusion exitCut, ?_⟩
            rw [stackExecutionCost_loop_run _ _ _ _ _ targetRun]
            simp only [compileResult, Option.map_some, StackSemControl.contLoop, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            change 2 + _ ≤ 2 + bodyBudget + recursiveBudget
            omega
        · have sourceExit : (wordSemExitLoop bodyResult,bodyPost) = (finalResult,finalSource) := by
            cases bodyResult with
            | none => exact tailRun
            | some result =>
              cases result <;> try exact tailRun
              next depth => cases depth <;> simp_all
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj sourceExit
          have targetExits : StackSemControl.contLoop (bodyResult.map compileResult) = false := by
            rw [contLoopCompile]
            cases h : wordSemContLoop bodyResult <;> simp_all
          have exitEq : StackSemControl.exitLoop (bodyResult.map compileResult) =
              (wordSemExitLoop bodyResult).map compileResult := by
            rw [exitLoopCompile]
            cases bodyResult with
            | none => rfl
            | some result =>
              cases result <;> simp_all
          refine ⟨bodyClock,targetBody,(wordSemExitLoop bodyResult).map compileResult,?_,?_,?_⟩
          · rw [← exitEq]
            exact runLoopExit compiledBody {target with clock := target.clock+bodyClock}
              targetBody (bodyResult.map compileResult) targetRun targetExits
          · exact exitRelation ac k f frame source cutSource bodyPost targetBody lens bodyResult
              (cutHandler names source cutSource cut) bodyConclusion
          · rw [stackExecutionCost_loop_run _ _ _ _ _ targetRun]
            simp only [targetExits, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            change 2 + _ ≤ 2 + bodyBudget + recursiveBudget
            omega

#print axioms compCorrectLoop
end InitECandidate.Runtime.WordToStack.ExecutedLoop
