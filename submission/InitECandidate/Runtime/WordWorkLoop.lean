import InitECandidate.Runtime.WordWork
import InitECandidate.Runtime.WordToStackLoopBudget

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.WordSemStateFiniteExact

def LoopWorkIH {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ cutSource bodyResult bodyPost,
    WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource ∧
    (bodyResult,bodyPost) = WordSemStateFiniteExact.evaluate body cutSource ∧
    wordSemContLoop bodyResult = true ∧ bodyPost.clock ≠ 0 →
    BoundedSimulation ac (wordSemSTOP (.loop names body exitNames))
      (WordSemStateFiniteExact.decClock bodyPost)
      (wordWork (wordSemSTOP (.loop names body exitNames)) (WordSemStateFiniteExact.decClock bodyPost))) ∧
  (∀ cutSource, WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource →
    BoundedSimulation ac body cutSource (wordWork body cutSource))

/-- Actual cut/body/reentry states fund the original complete Loop simulation.
No uniform or independent budget is supplied by the caller. -/
theorem wordWork_loop_correct {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : LoopWorkIH ac names exitNames body source) :
    BoundedSimulation ac (.loop names body exitNames) source
      (wordWork (.loop names body exitNames) source) := by
  cases cut : cutState (names, .ln) source with
  | none =>
      have vacuous : Loop.InductionHypotheses 0 0 ac names exitNames body source := by
        constructor
        · intro cutSource result post facts
          have impossible := facts.1
          rw [cut] at impossible
          cases impossible
        · intro cutSource facts
          rw [cut] at facts
          cases facts
      exact (Loop.compCorrectLoop 0 0 ac names exitNames body source vacuous).mono (Nat.zero_le _)
  | some cutSource =>
      rcases bodyRun : evaluate body cutSource with ⟨bodyResult, bodyPost⟩
      let bodyBudget := wordWork body cutSource
      let recursiveBudget := if wordSemContLoop bodyResult then
        (if bodyPost.clock = 0 then 0 else
          wordWork (wordSemSTOP (.loop names body exitNames))
            (Flapjack.WordSemStateFiniteExact.decClock bodyPost)) else 0
      have funded : bodyBudget + recursiveBudget ≤ wordWork (.loop names body exitNames) source := by
        rw [wordWork, cut]
        dsimp only
        rw [fix_clock_evaluate, bodyRun]
        dsimp only
        dsimp only [bodyBudget, recursiveBudget]
        split_ifs <;> omega
      have localIH : Loop.InductionHypotheses bodyBudget recursiveBudget ac names exitNames body source := by
        constructor
        · intro actualCut actualResult actualPost facts
          obtain ⟨actualCutRun, actualBodyRun, continues, nonzero⟩ := facts
          have sameCut := Option.some.inj (actualCutRun.symm.trans cut)
          subst actualCut
          obtain ⟨resultEq, postEq⟩ := Prod.mk.inj (actualBodyRun.trans bodyRun)
          subst actualResult
          subst actualPost
          have budgetEq : recursiveBudget = wordWork (wordSemSTOP (.loop names body exitNames))
              (Flapjack.WordSemStateFiniteExact.decClock bodyPost) := by
            simp only [recursiveBudget, continues, nonzero, if_true, if_false]
          rw [budgetEq]
          exact ih.1 cutSource bodyResult bodyPost ⟨cut, bodyRun.symm, continues, nonzero⟩
        · intro actualCut actualCutRun
          have sameCut := Option.some.inj (actualCutRun.symm.trans cut)
          subst actualCut
          exact ih.2 cutSource cut
      exact (Loop.compCorrectLoop bodyBudget recursiveBudget ac names exitNames body source localIH).mono funded

#print axioms wordWork_loop_correct
end InitECandidate.Runtime.WordToStack
