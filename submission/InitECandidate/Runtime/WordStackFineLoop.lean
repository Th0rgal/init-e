import InitECandidate.Runtime.WordStackExecutedLoop
import InitECandidate.Runtime.WordExecutionCostProps
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- An executed loop iteration preserves the same cost coefficient. The
body and re-entry hypotheses apply only at their actual source states. -/
theorem executedSimulation_loop {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (localBound : 2 ≤ factor * price (.loop names body exitNames) source)
    (bodyIH : ∀ cutSource, WordSemStateFiniteExact.cutState (names, .ln) source = some cutSource →
      ExecutedSimulation ac body cutSource (factor * wordExecutionCost price body cutSource))
    (recursiveIH : ∀ cutSource bodyResult bodyPost,
      WordSemStateFiniteExact.cutState (names, .ln) source = some cutSource →
      WordSemStateFiniteExact.evaluate body cutSource = (bodyResult, bodyPost) →
      wordSemContLoop bodyResult = true → bodyPost.clock ≠ 0 →
      ExecutedSimulation ac (wordSemSTOP (.loop names body exitNames))
        (WordSemStateFiniteExact.decClock bodyPost)
        (factor * wordExecutionCost price (wordSemSTOP (.loop names body exitNames))
          (WordSemStateFiniteExact.decClock bodyPost))) :
    ExecutedSimulation ac (.loop names body exitNames) source
      (factor * wordExecutionCost price (.loop names body exitNames) source) := by
  cases cut : WordSemStateFiniteExact.cutState (names, .ln) source with
  | none =>
    intro k f frame post target result bs bsPost n nPost compiled lens premises small
    have actual := premises.1
    rw [WordSemStateFiniteExact.evaluate, cut] at actual
    exact False.elim (premises.2.1 (congrArg Prod.fst actual.symm))
  | some cutSource =>
    rcases bodyRun : WordSemStateFiniteExact.evaluate body cutSource with ⟨bodyResult, bodyPost⟩
    let restWork := if wordSemContLoop bodyResult then
      if bodyPost.clock = 0 then 0 else
        wordExecutionCost price (wordSemSTOP (.loop names body exitNames))
          (WordSemStateFiniteExact.decClock bodyPost)
      else 0
    have ih : ExecutedLoop.InductionHypotheses
        (factor * wordExecutionCost price body cutSource) (factor * restWork)
        ac names exitNames body source := by
      constructor
      · intro otherCut otherResult otherPost guards
        rcases guards with ⟨otherCutRun, otherBodyRun, continues, positive⟩
        have cutEq : otherCut = cutSource := Option.some.inj (otherCutRun.symm.trans cut)
        subst otherCut
        have eq := Prod.mk.inj (otherBodyRun.trans bodyRun)
        obtain ⟨rfl, rfl⟩ := eq
        dsimp only [restWork]
        simp only [continues, positive, ↓reduceIte]
        exact recursiveIH _ _ _ otherCutRun otherBodyRun.symm continues positive
      · intro otherCut otherCutRun
        have cutEq : otherCut = cutSource := Option.some.inj (otherCutRun.symm.trans cut)
        subst otherCut
        exact bodyIH _ cut
    have simulation := ExecutedLoop.compCorrectLoop
      (factor * wordExecutionCost price body cutSource) (factor * restWork)
      ac names exitNames body source ih
    apply simulation.mono
    have cost : wordExecutionCost price (.loop names body exitNames) source =
        price (.loop names body exitNames) source + wordExecutionCost price body cutSource + restWork := by
      rw [wordExecutionCost, cut]
      dsimp only
      rw [WordSemStateFiniteExact.fix_clock_evaluate, bodyRun]
      rfl
    rw [cost, Nat.mul_add, Nat.mul_add]
    omega

#print axioms executedSimulation_loop
end InitECandidate.Runtime.WordToStack
