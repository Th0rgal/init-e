import InitECandidate.Runtime.WordStackRegisteredSimulation
import InitECandidate.Runtime.StackExecutionCostAddClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
namespace InitECandidate.Runtime.WordToStack.ExecutedSeq
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.StackToLab
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-! Additive sequence composition, retaining the actual first-run guard on
its second IH and all original early resource-limit result branches. -/
theorem compCorrectSeqFirstNonNone (firstBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ih : ExecutedSimulation ac first source firstBudget)
    (firstNonNone : (WordSemStateFiniteExact.evaluate first source).1 ≠ none) :
    ExecutedSimulation ac (.seq first second) source firstBudget := by
  apply executedSimulation_of_registers
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises small actualRegisters
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  rcases firstCompile : compNative ac false first (bs, n) (k, f, frame) with
    ⟨firstCode, middleBitmaps⟩
  rcases secondCompile : compNative ac false second middleBitmaps (k, f, frame) with
    ⟨secondCode, finalBitmaps⟩
  simp only [compNative, firstCompile, secondCompile] at compilation
  obtain ⟨compiledEq, bitmapEq⟩ := Prod.mk.inj compilation
  subst compiled
  have firstPrefix := compImpIsPrefix ac false second middleBitmaps (k, f, frame)
    secondCode finalBitmaps secondCompile
  rw [bitmapEq] at firstPrefix
  have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    apply labels loc
    rw [StackSem.getLabelsExact]
    exact Or.inl member
  have firstConventions : postAllocConventionsHOL k first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.1, conventions.2.1.1, conventions.2.2.1⟩
  have firstFlat : flatExpConventions first = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.1
  have firstMax : maxVarHOL first < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases firstRun : WordSemStateFiniteExact.evaluate first source with ⟨firstResult, middle⟩
  rw [firstRun] at firstNonNone execution
  cases firstResult with
  | none => exact False.elim (firstNonNone rfl)
  | some value =>
    obtain ⟨resultEq, sourceEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    obtain ⟨clock, targetPost, targetResult, targetRun, conclusion, firstCost⟩ :=
      ih k f frame middle target (some value) bs middleBitmaps.1 n middleBitmaps.2
        firstCode lens ⟨firstRun, notError, related, firstConventions, firstFlat,
          firstCompile, lengthBound, bitmapBound, firstPrefix.trans bitmapPrefix,
          firstLabels, firstMax⟩ small
    have firstCost := firstCost actualRegisters
    have targetNonNone : targetResult ≠ none := by
      intro eq
      subst targetResult
      simp [compCorrectResult] at conclusion
    refine ⟨clock, targetPost, targetResult, ?_, conclusion, ?_⟩
    · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, targetRun]
      cases targetResult with
      | none => exact False.elim (targetNonNone rfl)
      | some output => rfl
    · rw [stackExecutionCost_seq]
      simp only [show removalLocalPrice 6 riscvConfig.addrOffset (.seq firstCode secondCode) = 0 from rfl,
        Nat.zero_add, targetRun]
      cases targetResult with
      | none => exact False.elim (targetNonNone rfl)
      | some output => simpa only [Nat.add_zero] using firstCost

/-- A reached suffix adds its actual executed bound. The original early
resource-limit branch remains valid and stops before evaluating the suffix. -/
theorem compCorrectSeqFirstNone (firstBudget secondBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        ExecutedSimulation ac second middle secondBudget) ∧ ExecutedSimulation ac first source firstBudget)
    (firstNone : (WordSemStateFiniteExact.evaluate first source).1 = none) :
    ExecutedSimulation ac (.seq first second) source (firstBudget + secondBudget) := by
  classical
  apply executedSimulation_of_registers
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises small actualRegisters
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  rcases firstCompile : compNative ac false first (bs, n) (k, f, frame) with
    ⟨firstCode, middleBitmaps⟩
  rcases secondCompile : compNative ac false second middleBitmaps (k, f, frame) with
    ⟨secondCode, finalBitmaps⟩
  simp only [compNative, firstCompile, secondCompile] at compilation
  obtain ⟨compiledEq, bitmapEq⟩ := Prod.mk.inj compilation
  subst compiled
  have firstPrefix := compImpIsPrefix ac false second middleBitmaps (k, f, frame)
    secondCode finalBitmaps secondCompile
  rw [bitmapEq] at firstPrefix
  have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    apply labels loc
    rw [StackSem.getLabelsExact]
    exact Or.inl member
  have firstConventions : postAllocConventionsHOL k first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.1, conventions.2.1.1, conventions.2.2.1⟩
  have firstFlat : flatExpConventions first = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.1
  have firstMax : maxVarHOL first < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  have secondConventions : postAllocConventionsHOL k second = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.2, conventions.2.1.2, conventions.2.2.2⟩
  have secondFlat : flatExpConventions second = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.2
  have secondMax : maxVarHOL second < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases firstRun : WordSemStateFiniteExact.evaluate first source with ⟨firstResult, middle⟩
  rw [firstRun] at firstNone execution
  cases firstResult with
  | some value => cases firstNone
  | none =>
    obtain ⟨clock, targetMiddle, firstTargetResult, targetRun, firstConclusion, firstCost⟩ :=
      ih.2 k f frame middle target none bs middleBitmaps.1 n middleBitmaps.2
        firstCode lens ⟨firstRun, by simp, related, firstConventions, firstFlat,
          firstCompile, lengthBound, bitmapBound, firstPrefix.trans bitmapPrefix,
          firstLabels, firstMax⟩ small
    have firstCost := firstCost actualRegisters
    cases firstTargetResult with
    | some value =>
      simp [compCorrectResult] at firstConclusion
      rcases firstConclusion with ⟨valueEq, events, resource⟩
      subst value
      have finalEvents := WordSemStateFiniteExact.evaluate_io_events_mono
        second middle result sourcePost execution
      have resourceThe : miscThe (middle.stackLimit + 1) middle.stackMax > middle.stackLimit := by
        cases h : middle.stackMax <;> simp_all [miscThe]
      have finalResourceThe := WordSemStateFiniteExact.evaluate_stack_limit_stack_max
        second middle result sourcePost ⟨execution, resourceThe⟩
      have finalResource : sourcePost.stackMax.getD (sourcePost.stackLimit + 1) >
          sourcePost.stackLimit := by
        cases h : sourcePost.stackMax <;> simp_all [miscThe]
      have dimension : goodDimindex 64 := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have mismatch : result.map compileResult ≠ some (.halt (.word 2)) := by
        cases result with
        | none => simp
        | some value =>
          simp only [Option.map_some, ne_eq, Option.some.injEq]
          exact Ne.symm ((haltEqCompileResult value).2 dimension)
      refine ⟨clock, targetMiddle, some (.halt (.word 2)), ?_, ?_, ?_⟩
      · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, targetRun]
        rfl
      · unfold compCorrectResult
        split
        · exact ⟨rfl, events.trans finalEvents, finalResource⟩
        · rename_i equal
          exact False.elim (mismatch (by simpa using equal))
      · rw [stackExecutionCost_seq]
        simp only [show removalLocalPrice 6 riscvConfig.addrOffset (.seq firstCode secondCode) = 0 from rfl,
          Nat.zero_add, targetRun, Nat.add_zero]
        exact firstCost.trans (Nat.le_add_right firstBudget secondBudget)
    | none =>
      simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false,
        ↓reduceIte] at firstConclusion
      have accounting := compImpLength ac false first (bs, n) (k, f, frame)
        firstCode middleBitmaps ⟨firstCompile, lengthBound⟩
      have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
        firstCode {target with clock := target.clock + clock} targetMiddle none targetRun
      have gap := accounting.2
      have secondBitmapBound : middleBitmaps.2 - (appListAppend middleBitmaps.1).length ≤
          targetMiddle.bitmaps.length := by
        rw [← gap]
        exact bitmapBound.trans mono.1.length_le
      have secondPrefix : (appListAppend finalBitmaps.1).IsPrefix
          (targetMiddle.bitmaps.drop
            (middleBitmaps.2 - (appListAppend middleBitmaps.1).length)) := by
        rw [← gap, bitmapEq]
        exact bitmapPrefix.trans (mono.1.drop _)
      have secondLabels : ∀ loc, StackSem.getLabelsExact secondCode loc →
          StackSem.locCheckExact targetMiddle.code loc := by
        intro loc member
        apply LocationLabels.locCheckSubset target.code targetMiddle.code mono.2 loc
        apply labels loc
        rw [StackSem.getLabelsExact]
        exact Or.inr member
      obtain ⟨secondClock, targetPost, targetResult, secondRun, conclusion, secondCost⟩ :=
        ih.1 none middle ⟨firstRun.symm, rfl⟩ k f frame sourcePost targetMiddle
          result middleBitmaps.1 finalBitmaps.1 middleBitmaps.2 finalBitmaps.2
          secondCode lens ⟨execution, notError, firstConclusion, secondConventions,
            secondFlat, secondCompile, accounting.1, secondBitmapBound, secondPrefix,
            secondLabels, secondMax⟩ small
      have secondCost := secondCost actualRegisters
      have extendedFirst := Flapjack.Compiler.Backend.StackProps.evaluateAddClock
        secondClock firstCode {target with clock := target.clock + clock}
        none targetMiddle ⟨targetRun, by simp⟩
      have handlerEq : middle.handler = source.handler := by
        have preserved := WordSemStackEq.evaluateStackSwap first source
        unfold WordSemStackEq.stackSwapPost at preserved
        rw [firstRun] at preserved
        exact preserved.2.1
      have finalConclusion : compCorrectResult ac k f frame source sourcePost
          targetPost result targetResult lens := by
        unfold compCorrectResult at conclusion ⊢
        rw [handlerEq] at conclusion
        exact conclusion
      refine ⟨clock + secondClock, targetPost, targetResult, ?_, finalConclusion, ?_⟩
      · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
        have clockEq : {target with clock := target.clock + (clock + secondClock)} =
            {{target with clock := target.clock + clock} with
              clock := (target.clock + clock) + secondClock} := by
          simp only [Nat.add_assoc]
        rw [clockEq, extendedFirst]
        exact secondRun
      · have firstCostExtended := stackExecutionCost_addClock
          (removalLocalPrice 6 riscvConfig.addrOffset) firstCode
          {target with clock := target.clock + clock} targetMiddle none targetRun (by simp) secondClock
        have clockEq : {target with clock := target.clock + (clock + secondClock)} =
            {{target with clock := target.clock + clock} with
              clock := (target.clock + clock) + secondClock} := by
          simp only [Nat.add_assoc]
        rw [clockEq, stackExecutionCost_seq]
        simp only [show removalLocalPrice 6 riscvConfig.addrOffset (.seq firstCode secondCode) = 0 from rfl,
          Nat.zero_add, extendedFirst]
        rw [firstCostExtended]
        exact Nat.add_le_add firstCost secondCost

/-- Quantitative Seq constructor assembled from the original first-run
NONE/non-NONE split, with no extra branch or target-run hypothesis. -/
theorem compCorrectSeq (firstBudget secondBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        ExecutedSimulation ac second middle secondBudget) ∧ ExecutedSimulation ac first source firstBudget) :
    ExecutedSimulation ac (.seq first second) source (firstBudget + secondBudget) := by
  by_cases guard : (WordSemStateFiniteExact.evaluate first source).1 = none
  · exact compCorrectSeqFirstNone firstBudget secondBudget ac first second source ih guard
  · exact (compCorrectSeqFirstNonNone firstBudget ac first second source ih.2 guard).mono
      (Nat.le_add_right firstBudget secondBudget)


#print axioms compCorrectSeq
end InitECandidate.Runtime.WordToStack.ExecutedSeq
