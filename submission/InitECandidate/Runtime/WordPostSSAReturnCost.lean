import InitECandidate.Runtime.WordPostSSATailCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 5000000

/-- Code replacement commutes with restoring a caller frame. -/
theorem popEnv_with_code {C F : Type} (source : WordSemStateFiniteExact 64 C F)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) :
    popEnv {source with code := code} = (popEnv source).map (fun post => {post with code := code}) := by
  unfold popEnv
  dsimp only
  split <;> rfl

/-- Actual returning calls without an exception handler, through the
concrete optimized table. Both the callee and the selected continuation use
strictly smaller execution clocks. All final state and cost alignment is
proved from those guarded instances and the local optimizer theorem. -/
theorem postSSACodeTable_return_execution {C F : Type}
    (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (destination : Option Nat) (arguments : List Nat) (source : WordSemStateFiniteExact 64 C F)
    (codeFree : WordProps.noInstallCode source.code) (codeFlat : PostSSAFlatCode source.code)
    (free : noInstallSubprogsHOL continuation = true)
    (safe : (evaluate (.call (some (values, names, continuation, l1, l2))
      destination arguments none) source).1 ≠ some .error)
    (ih : PostSSACodeTransportIH (C := C) (F := F) source.termdep source.clock) :
    evaluate (.call (some (values, names, continuation, l1, l2)) destination arguments none)
        {source with code := postSSACodeTable source.code} =
      ((evaluate (.call (some (values, names, continuation, l1, l2)) destination arguments none) source).1,
        {(evaluate (.call (some (values, names, continuation, l1, l2)) destination arguments none) source).2 with
          code := postSSACodeTable source.code}) ∧
    wordExecutionCost wordOptimizerLocalPrice
        (.call (some (values, names, continuation, l1, l2)) destination arguments none)
        {source with code := postSSACodeTable source.code} ≤
      wordExecutionCost wordOptimizerLocalPrice
        (.call (some (values, names, continuation, l1, l2)) destination arguments none) source := by
  rw [WordToWord.evaluate_call_eq] at safe
  rcases hg : getVars arguments source with _ | xs
  · simp only [hg] at safe
    exact (safe rfl).elim
  simp only [hg] at safe
  by_cases bad : wordSemBadDestArgs destination arguments = true
  · simp only [bad, if_true] at safe
    exact (safe rfl).elim
  have good : wordSemBadDestArgs destination arguments = false := by simpa using bad
  simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc] at safe
  rcases found : wordSemFindCode destination (.loc l1 l2 :: xs) source.code source.stackSize with
    _ | ⟨actualArguments, body, size⟩
  · simp only [found] at safe
    exact (safe rfl).elim
  simp only [found] at safe
  by_cases badNames : sptDomainEmpty names.1 ∨ ¬ values.Nodup
  · simp only [badNames, if_true] at safe
    exact (safe rfl).elim
  simp only [badNames, if_false] at safe
  rcases cut : wordSemCutEnvs names source.locals with _ | envs
  · simp only [cut] at safe
    exact (safe rfl).elim
  simp only [cut] at safe
  let target : WordSemStateFiniteExact 64 C F := {source with code := postSSACodeTable source.code}
  have targetVars : getVars arguments target = some xs := by
    rw [(getVars_congr target source rfl arguments).symm]
    exact hg
  have targetFound : wordSemFindCode destination (.loc l1 l2 :: xs) target.code target.stackSize =
      some (actualArguments, postSSAOptimize body, size) := by
    rw [show target.code = postSSACodeTable source.code from rfl,
      show target.stackSize = source.stackSize from rfl, postSSACodeTable_findCode, found]
    rfl
  have targetCut : wordSemCutEnvs names target.locals = some envs := cut
  have targetClock : target.clock = source.clock := rfl
  change evaluate (.call (some (values, names, continuation, l1, l2)) destination arguments none) target = _ ∧
    wordExecutionCost wordOptimizerLocalPrice
      (.call (some (values, names, continuation, l1, l2)) destination arguments none) target ≤ _
  by_cases zero : source.clock = 0
  · constructor
    · rw [WordToWord.evaluate_call_eq, targetVars]
      simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, targetFound, badNames,
        targetCut, targetClock, zero, if_true]
      rw [WordToWord.evaluate_call_eq, hg]
      simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found, badNames, cut, zero, if_true]
      rfl
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [targetVars, hg, good, Bool.false_eq_true, if_false, wordSemAddRetLoc,
        targetFound, found, badNames, targetCut, cut, targetClock, zero, dif_pos rfl]
      simpa only [dif_pos True.intro] using
        le_of_eq (wordOptimizerLocalPrice_state_independent
          (.call (some (values, names, continuation, l1, l2)) destination arguments none) target source)
  simp only [zero, if_false] at safe
  let entry := WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs none (decClock source))
  rcases actual : evaluate body entry with ⟨result, post⟩
  have entryRun : evaluate body (WordSemStateFiniteExact.callEnv actualArguments size
      (pushEnv envs none (decClock source))) = (result, post) := actual
  rw [entryRun] at safe
  have resultSafe : result ≠ some .error := by
    intro badResult
    rw [badResult] at safe
    exact safe rfl
  have terminal : result ≠ none ∧ (∀ label, result ≠ some (.break label)) ∧
      (∀ label, result ≠ some (.continue label)) := by
    cases result with
    | none => exact (safe rfl).elim
    | some outcome => cases outcome <;> simp_all
  have smaller : Prod.Lex (· < ·) (· < ·)
      (entry.termdep, entry.clock) (source.termdep, source.clock) := by
    simp only [entry, WordSemStateFiniteExact.callEnv, pushEnv_clock, pushEnv_termdep, decClock]
    apply Prod.Lex.right
    omega
  have bodyFree := WordProps.noInstallFindCode source.code destination (.loc l1 l2 :: xs)
    source.stackSize actualArguments body size ⟨codeFree, found⟩
  obtain ⟨label, arity, lookup⟩ := WordProps.findCode_lookup source.code destination (.loc l1 l2 :: xs)
    source.stackSize actualArguments body size found
  have bodyFlat := codeFlat label arity body lookup
  obtain ⟨transported, transportCost⟩ := ih body entry post result smaller bodyFree
    codeFree codeFlat actual resultSafe
  obtain ⟨optimized, optimizeCost⟩ := postSSAOptimize_terminal_execution config body
    {entry with code := postSSACodeTable entry.code}
    {post with code := postSSACodeTable entry.code} result bodyFlat transported resultSafe terminal
  have targetEntry : WordSemStateFiniteExact.callEnv actualArguments size
      (pushEnv envs none (decClock target)) = {entry with code := postSSACodeTable entry.code} := rfl
  have targetRun : evaluate (postSSAOptimize body)
      (WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs none (decClock target))) =
        (result, {post with code := postSSACodeTable source.code}) := by
    rw [targetEntry]
    exact optimized
  have sourceEq := WordToWord.evaluate_call_eq source
    (some (values, names, continuation, l1, l2)) none destination arguments
  simp only [hg, good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found,
    badNames, cut, zero, entryRun] at sourceEq
  have targetEq := WordToWord.evaluate_call_eq target
    (some (values, names, continuation, l1, l2)) none destination arguments
  simp only [targetVars, good, Bool.false_eq_true, if_false, wordSemAddRetLoc, targetFound,
    badNames, targetCut, targetClock, zero, targetRun] at targetEq
  have costSource := ret_call_cost wordOptimizerLocalPrice values names continuation l1 l2
    destination arguments none source xs hg good actualArguments body size found badNames envs cut
    zero result post entryRun
  have costTarget := ret_call_cost wordOptimizerLocalPrice values names continuation l1 l2
    destination arguments none target xs targetVars good actualArguments (postSSAOptimize body) size
    targetFound badNames envs targetCut zero result {post with code := postSSACodeTable source.code} targetRun
  have bodyCost : wordExecutionCost wordOptimizerLocalPrice (postSSAOptimize body)
      (WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs none (decClock target))) ≤
        wordExecutionCost wordOptimizerLocalPrice body entry := by
    rw [targetEntry]
    exact optimizeCost.trans transportCost
  have headEq := wordOptimizerLocalPrice_state_independent
    (.call (some (values, names, continuation, l1, l2)) destination arguments none) target source
  suffices after :
      evaluate (.call (some (values, names, continuation, l1, l2)) destination arguments none) target =
        ((evaluate (.call (some (values, names, continuation, l1, l2)) destination arguments none) source).1,
          {(evaluate (.call (some (values, names, continuation, l1, l2)) destination arguments none) source).2 with
            code := postSSACodeTable source.code}) ∧
      retCont wordOptimizerLocalPrice values continuation l1 l2 none envs result
          {post with code := postSSACodeTable source.code} ≤
        retCont wordOptimizerLocalPrice values continuation l1 l2 none envs result post by
    refine ⟨after.1, ?_⟩
    rw [costTarget, costSource, headEq]
    exact Nat.add_le_add (Nat.add_le_add_left bodyCost _) after.2
  cases result with
  | none => exact (terminal.1 rfl).elim
  | some outcome =>
    cases outcome with
    | result location returned =>
      by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
      · simp only [invalid, if_true] at safe
        exact (safe rfl).elim
      simp only [invalid, if_false] at safe
      rcases popped : popEnv post with _ | restored
      · simp only [popped] at safe
        exact (safe rfl).elim
      simp only [popped] at safe
      by_cases domain : sptDomainEqUnion restored.locals envs.1 envs.2
      · simp only [domain, if_true] at safe
        rcases nextRun : evaluate continuation (setVars values returned restored) with ⟨nextResult, nextPost⟩
        have nextSafe : nextResult ≠ some .error := by simpa only [nextRun] using safe
        have restoredFields := WordToWord.popEnv_fields popped
        have bodyClock := evaluate_clock body entry (some (.result location returned)) post actual
        have postCode : post.code = source.code := by
          have h := code_evaluate body entry bodyFree codeFree
          rw [actual] at h
          exact h
        have restoredCode : restored.code = source.code := restoredFields.1.trans postCode
        have nextCode : (setVars values returned restored).code = source.code := restoredCode
        have nextSmaller : Prod.Lex (· < ·) (· < ·)
            ((setVars values returned restored).termdep, (setVars values returned restored).clock)
            (source.termdep, source.clock) := by
          have dep := popEnv_termdep post restored popped
          have ck := popEnv_clock post restored popped
          simp only [entry, WordSemStateFiniteExact.callEnv, pushEnv_termdep, pushEnv_clock, decClock] at bodyClock
          simp only [setVars]
          rw [dep, bodyClock.2]
          apply Prod.Lex.right
          omega
        have nextFree : WordProps.noInstallCode (setVars values returned restored).code := nextCode.symm ▸ codeFree
        have nextFlat : PostSSAFlatCode (setVars values returned restored).code := nextCode.symm ▸ codeFlat
        obtain ⟨nextTargetRun, nextCost⟩ := ih continuation (setVars values returned restored)
          nextPost nextResult nextSmaller free nextFree nextFlat nextRun nextSafe
        have nextEntry : setVars values returned {restored with code := postSSACodeTable source.code} =
            {(setVars values returned restored) with code := postSSACodeTable ((setVars values returned restored).code)} := by
          rw [nextCode]
          rfl
        have mappedPop : popEnv {post with code := postSSACodeTable source.code} =
            some {restored with code := postSSACodeTable source.code} := by
          rw [popEnv_with_code, popped]
          rfl
        constructor
        · rw [sourceEq, targetEq]
          simp only [invalid, if_false, popped, mappedPop, domain, if_true]
          rw [nextEntry, nextTargetRun, nextRun, nextCode]
        · simp only [retCont, invalid, if_false, popped, mappedPop, domain, if_true]
          rw [nextEntry]
          exact nextCost
      · simp only [domain, if_false] at safe
        exact (safe rfl).elim
    | «break» label => exact (terminal.2.1 label rfl).elim
    | «continue» label => exact (terminal.2.2 label rfl).elim
    | error => exact (resultSafe rfl).elim
    | exception _ _ | timeOut | notEnoughSpace | finalFfi _ =>
      constructor
      · rw [sourceEq, targetEq]
      · simp only [retCont, Nat.le_refl]

#print axioms popEnv_with_code
#print axioms postSSACodeTable_return_execution
end InitECandidate.Runtime.FineCost
