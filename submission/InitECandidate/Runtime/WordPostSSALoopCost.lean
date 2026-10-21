import InitECandidate.Runtime.WordPostSSAControlCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Cutting the local environment commutes with code replacement. -/
theorem cutState_with_code {C F : Type} (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact 64 C F) (code : Spt (Nat × WordLangProgHOL (BitVec 64))) :
    cutState names {source with code := code} =
      (cutState names source).map (fun post => {post with code := code}) := by
  unfold cutState
  dsimp only
  split <;> rfl

theorem cutState_code {C F : Type} (names : WordLangCutsetsHOL)
    (source post : WordSemStateFiniteExact 64 C F) (cut : cutState names source = some post) :
    post.code = source.code := by
  unfold cutState at cut
  split at cut
  · cases cut
  · cases cut
    rfl

/-- A loop transports its actual reached body and recursive iteration. This
proof uses the actual cut states and post states; it requires neither equal
arbitrary locals domains nor an allowance proportional to initial fuel. -/
theorem postSSA_loop_transport {C F : Type}
    (names exits : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (free : noInstallSubprogsHOL body = true) (codeFree : WordProps.noInstallCode source.code)
    (bodyTransfer : ∀ cutSource, cutState (names, .ln) source = some cutSource →
      PostSSATransportAt body cutSource)
    (nextTransfer : ∀ cutSource result middle,
      cutState (names, .ln) source = some cutSource →
      evaluate body cutSource = (result, middle) → wordSemContLoop result = true → middle.clock ≠ 0 →
      PostSSATransportAt (.loop names body exits) (decClock middle)) :
    PostSSATransportAt (.loop names body exits) source := by
  intro safe
  rcases cut : cutState (names, .ln) source with _ | cutSource
  · rw [evaluate, cut] at safe
    exact (safe rfl).elim
  rcases actual : evaluate body cutSource with ⟨result, middle⟩
  have bodySafe : (evaluate body cutSource).1 ≠ some .error := by
    intro bad
    have error : result = some .error := by simpa only [actual] using bad
    rw [evaluate, cut] at safe
    dsimp only at safe
    rw [fix_clock_evaluate, actual, error] at safe
    simpa [wordSemContLoop, wordSemExitLoop] using safe
  have cutCode := cutState_code (names, .ln) source cutSource cut
  obtain ⟨bodyRun, bodyCost⟩ := bodyTransfer cutSource cut bodySafe
  rw [actual, cutCode] at bodyRun
  rw [cutCode] at bodyCost
  have cutFree : WordProps.noInstallCode cutSource.code := cutCode.symm ▸ codeFree
  have middleCode : middle.code = source.code := by
    have h := code_evaluate body cutSource free cutFree
    rw [actual] at h
    exact h.trans cutCode
  let target : WordSemStateFiniteExact 64 C F := {source with code := postSSACodeTable source.code}
  have targetCut : cutState (names, .ln) target =
      some {cutSource with code := postSSACodeTable source.code} := by
    rw [show target = {source with code := postSSACodeTable source.code} from rfl,
      cutState_with_code, cut]
    rfl
  have sourceEq := WordToWord.evaluate_loop_run names exits body source cutSource cut result middle actual
  have targetEq := WordToWord.evaluate_loop_run names exits body target
    {cutSource with code := postSSACodeTable source.code} targetCut result
    {middle with code := postSSACodeTable source.code} bodyRun
  have sourceCost : wordExecutionCost wordOptimizerLocalPrice (.loop names body exits) source =
      2 + wordExecutionCost wordOptimizerLocalPrice body cutSource +
        if wordSemContLoop result then
          (if middle.clock = 0 then 0 else wordExecutionCost wordOptimizerLocalPrice
            (.loop names body exits) (decClock middle)) else 0 := by
    rw [wordExecutionCost, cut]
    dsimp only
    rw [fix_clock_evaluate, actual]
    simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, wordSemSTOP]
    split_ifs <;> rfl
  have targetCost : wordExecutionCost wordOptimizerLocalPrice (.loop names body exits) target =
      2 + wordExecutionCost wordOptimizerLocalPrice body
        {cutSource with code := postSSACodeTable source.code} +
        if wordSemContLoop result then
          (if middle.clock = 0 then 0 else wordExecutionCost wordOptimizerLocalPrice
            (.loop names body exits) (decClock {middle with code := postSSACodeTable source.code})) else 0 := by
    rw [wordExecutionCost, targetCut]
    dsimp only
    rw [fix_clock_evaluate, bodyRun]
    simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, wordSemSTOP]
    split_ifs <;> rfl
  change evaluate (.loop names body exits) target = _ ∧
    wordExecutionCost wordOptimizerLocalPrice (.loop names body exits) target ≤ _
  by_cases continuing : wordSemContLoop result = true
  · by_cases zero : middle.clock = 0
    · constructor
      · rw [sourceEq, targetEq]
        simp only [continuing, if_true]
        rw [if_pos zero, if_pos zero]
        rfl
      · rw [sourceCost, targetCost]
        simp only [continuing, if_true, zero, Nat.add_zero]
        exact Nat.add_le_add_left bodyCost 2
    · have nextSafe : (evaluate (.loop names body exits) (decClock middle)).1 ≠ some .error := by
        rw [sourceEq] at safe
        simpa only [continuing, if_true, zero, if_false] using safe
      obtain ⟨nextRun, nextCost⟩ := nextTransfer cutSource result middle cut actual continuing zero nextSafe
      change evaluate (.loop names body exits) {decClock middle with code := postSSACodeTable middle.code} = _ at nextRun
      change wordExecutionCost wordOptimizerLocalPrice (.loop names body exits)
        {decClock middle with code := postSSACodeTable middle.code} ≤ _ at nextCost
      simp only [show (decClock middle).code = middle.code from rfl, middleCode] at nextRun nextCost
      constructor
      · rw [sourceEq, targetEq]
        simp only [continuing, if_true]
        rw [if_neg zero, if_neg zero]
        exact nextRun
      · rw [sourceCost, targetCost]
        simp only [continuing, if_true, zero, if_false]
        exact Nat.add_le_add (Nat.add_le_add_left bodyCost 2) nextCost
  · constructor
    · rw [sourceEq, targetEq]
      simp only [continuing, Bool.false_eq_true, if_false]
      by_cases breaking : result = some (.break 0)
      · simp only [breaking, if_true]
        rw [cutState_with_code]
        cases cutState (exits, .ln) middle <;> rfl
      · simp only [breaking, if_false]
    · rw [sourceCost, targetCost]
      simp only [continuing, if_false, Nat.add_zero]
      exact Nat.add_le_add_left bodyCost 2

#print axioms cutState_with_code
#print axioms cutState_code
#print axioms postSSA_loop_transport
end InitECandidate.Runtime.FineCost
