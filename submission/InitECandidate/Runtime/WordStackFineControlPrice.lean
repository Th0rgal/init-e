import InitECandidate.Runtime.WordExecutionCostProps
import InitECandidate.Runtime.WordStackExecutedSeq
import InitECandidate.Runtime.WordStackExecutedIf
import InitECandidate.Runtime.WordStackExecutedLoop
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost
/-- Sequence transfer follows the source's executed suffix exactly. In
particular, an early return pays no cost for the unexecuted second statement.
The coefficient is unchanged by composition. -/
theorem executedSimulation_seqWithPrice (targetPrice : StackLang.HolProg 64 → Nat)
    (freeSeq : ∀ a b, targetPrice (.seq a b) = 0) {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (free : price (.seq first second) source = 0)
    (firstIH : ExecutedSimulationFor targetPrice ac first source (factor * wordExecutionCost price first source))
    (secondIH : ∀ middle, WordSemStateFiniteExact.evaluate first source = (none, middle) →
      ExecutedSimulationFor targetPrice ac second middle (factor * wordExecutionCost price second middle)) :
    ExecutedSimulationFor targetPrice ac (.seq first second) source
      (factor * wordExecutionCost price (.seq first second) source) := by
  rcases actual : WordSemStateFiniteExact.evaluate first source with ⟨result, middle⟩
  have cost := wordExecutionCost_seq price first second source
  rw [free, Nat.zero_add, actual] at cost
  cases result with
  | none =>
    have simulation := ExecutedSeq.compCorrectSeqFirstNoneWithPrice targetPrice freeSeq
      (factor * wordExecutionCost price first source)
      (factor * wordExecutionCost price second middle) ac first second source
      ⟨?_, firstIH⟩ (by simp only [actual])
    · simpa only [cost, Nat.mul_add] using simulation
    · intro output post run
      have equal : (output, post) = (none, middle) := run.1.trans actual
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact secondIH _ actual
  | some value =>
    have simulation := ExecutedSeq.compCorrectSeqFirstNonNoneWithPrice targetPrice freeSeq
      (factor * wordExecutionCost price first source) ac first second source firstIH
      (by simp only [actual, ne_eq, reduceCtorEq, not_false_eq_true])
    simpa only [cost, Nat.add_zero] using simulation


private theorem wordCost_ite_selectedFor {F : Type}
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (comparison : Cmp) (register : Nat) (operand : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (x y : WordLocW 64) (value : Bool)
    (left : WordSemStateFiniteExact.getVar register source = some x)
    (right : WordSemStateFiniteExact.getVarImm operand source = some y)
    (compared : wordSemWordCmp comparison x y = some value) :
    wordExecutionCost price (.ite comparison register operand first second) source =
      price (.ite comparison register operand first second) source +
        wordExecutionCost price (if value then first else second) source := by
  rw [wordExecutionCost]
  simp only [left, right, compared]
  cases value <;> rfl

/-- Conditional transfer charges only the branch selected by the actual
source comparison. Its coefficient does not grow with nesting depth. -/
theorem executedSimulation_iteWithPrice (targetPrice : StackLang.HolProg 64 → Nat)
    (loadPrice constPrice branchPrice overhead : Nat)
    (targetCaps : InitECandidate.Runtime.StackToLab.ConditionPriceCaps targetPrice loadPrice constPrice branchPrice overhead) {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec 64)) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (localBound : overhead ≤ factor * price (.ite comparison register operand first second) source)
    (firstIH : ∀ x y,
      WordSemStateFiniteExact.getVar register source = some x →
      WordSemStateFiniteExact.getVarImm operand source = some y →
      wordSemWordCmp comparison x y = some true →
      ExecutedSimulationFor targetPrice ac first source (factor * wordExecutionCost price first source))
    (secondIH : ∀ x y,
      WordSemStateFiniteExact.getVar register source = some x →
      WordSemStateFiniteExact.getVarImm operand source = some y →
      wordSemWordCmp comparison x y = some false →
      ExecutedSimulationFor targetPrice ac second source (factor * wordExecutionCost price second source)) :
    ExecutedSimulationFor targetPrice ac (.ite comparison register operand first second) source
      (factor * wordExecutionCost price (.ite comparison register operand first second) source) := by
  let p : WordLangProgHOL (BitVec 64) := .ite comparison register operand first second
  have ih : ExecutedIf.OriginalInductionHypothesesFor targetPrice
      (factor * (wordExecutionCost price p source - price p source))
      ac comparison register operand first second source := by
    constructor
    · intro v3 v4 x y value guards
      rcases guards with ⟨pair, rfl, rfl, compared, rfl⟩
      have reads := Prod.mk.inj pair
      have cost := wordCost_ite_selectedFor price comparison register operand first second source
        x y true reads.1 reads.2 compared
      change ExecutedSimulationFor targetPrice ac first source
        (factor * (wordExecutionCost price (.ite comparison register operand first second) source -
          price (.ite comparison register operand first second) source))
      rw [cost, Nat.add_sub_cancel_left]
      exact firstIH x y reads.1 reads.2 compared
    · intro v3 v4 x y value guards
      rcases guards with ⟨pair, rfl, rfl, compared, selected⟩
      have valueFalse : value = false := by cases value <;> simp_all
      subst value
      have reads := Prod.mk.inj pair
      have cost := wordCost_ite_selectedFor price comparison register operand first second source
        x y false reads.1 reads.2 compared
      change ExecutedSimulationFor targetPrice ac second source
        (factor * (wordExecutionCost price (.ite comparison register operand first second) source -
          price (.ite comparison register operand first second) source))
      rw [cost, Nat.add_sub_cancel_left]
      exact secondIH x y reads.1 reads.2 compared
  have simulation := ExecutedIf.compCorrectIfWithPrice targetPrice loadPrice constPrice branchPrice overhead targetCaps
    (factor * (wordExecutionCost price p source - price p source))
    ac comparison register operand first second source ih
  apply simulation.mono
  have localLe : price p source ≤ wordExecutionCost price p source := by
    rw [wordExecutionCost]
    exact Nat.le_add_right _ _
  have accounting : factor * (wordExecutionCost price p source - price p source) +
      factor * price p source = factor * wordExecutionCost price p source := by
    rw [← Nat.mul_add, Nat.sub_add_cancel localLe]
  change factor * (wordExecutionCost price p source - price p source) + overhead ≤
    factor * wordExecutionCost price p source
  change overhead ≤ factor * price p source at localBound
  omega


/-- An executed loop iteration preserves the same cost coefficient. The
body and re-entry hypotheses apply only at their actual source states. -/
theorem executedSimulation_loopWithPrice (targetPrice : StackLang.HolProg 64 → Nat)
    (loopNode : ∀ body, targetPrice (.loop body) = 2) {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (localBound : 2 ≤ factor * price (.loop names body exitNames) source)
    (bodyIH : ∀ cutSource, WordSemStateFiniteExact.cutState (names, .ln) source = some cutSource →
      ExecutedSimulationFor targetPrice ac body cutSource (factor * wordExecutionCost price body cutSource))
    (recursiveIH : ∀ cutSource bodyResult bodyPost,
      WordSemStateFiniteExact.cutState (names, .ln) source = some cutSource →
      WordSemStateFiniteExact.evaluate body cutSource = (bodyResult, bodyPost) →
      wordSemContLoop bodyResult = true → bodyPost.clock ≠ 0 →
      ExecutedSimulationFor targetPrice ac (wordSemSTOP (.loop names body exitNames))
        (WordSemStateFiniteExact.decClock bodyPost)
        (factor * wordExecutionCost price (wordSemSTOP (.loop names body exitNames))
          (WordSemStateFiniteExact.decClock bodyPost))) :
    ExecutedSimulationFor targetPrice ac (.loop names body exitNames) source
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
    have ih : ExecutedLoop.InductionHypothesesFor targetPrice
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
    have simulation := ExecutedLoop.compCorrectLoopWithPrice targetPrice loopNode
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


#print axioms executedSimulation_seqWithPrice
#print axioms executedSimulation_iteWithPrice
#print axioms executedSimulation_loopWithPrice
end InitECandidate.Runtime.WordToStack
