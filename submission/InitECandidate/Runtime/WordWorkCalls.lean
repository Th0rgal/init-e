import InitECandidate.Runtime.WordWorkCallSelection
import InitECandidate.Runtime.WordToStackCallBudget
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Encoders.Asm

def CallWorkIH {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x ys s1,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc originalL1 originalL2 ∨ ys.length ≠ n.length) ∧
        WordSemStateFiniteExact.popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
      BoundedSimulation ac retHandler (WordSemStateFiniteExact.setVars n ys s1) (wordWork retHandler (WordSemStateFiniteExact.setVars n ys s1))) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x' y v n' v2 h
        v4 originalL1' originalL2',
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
        v4 = (originalL1', originalL2') ∧ x' = .loc originalL1' originalL2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
      BoundedSimulation ac h (WordSemStateFiniteExact.setVar n' y s2) (wordWork h (WordSemStateFiniteExact.setVar n' y s2))) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 →
      BoundedSimulation ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) (wordWork prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))))) ∧
    (∀ xs v3 args1 v10 prog ss,
      WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
      wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
      v3 = (args1,v10) ∧ v10 = (prog,ss) ∧ ret = none ∧ handler = none ∧ source.clock ≠ 0 →
      BoundedSimulation ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source)) (wordWork prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source))))


/-- Original guarded Call recursion funded at the actual source states. -/
theorem wordWork_call_correct {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : CallWorkIH ac ret dest args handler source) :
    BoundedSimulation ac (.call ret dest args handler) source
      (wordWork (.call ret dest args handler) source) := by
  let budgets := callWorkBudgets ret dest args handler source
  have localIH : Call.OriginalInductionHypotheses budgets.1 budgets.2.1 budgets.2.2
      ac ret dest args handler source := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2
        envs v5 s2 v8 x ys s1 facts
      have child := ih.1 xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11
        originalL1 originalL2 envs v5 s2 v8 x ys s1 facts
      rcases facts with ⟨get, bad, find, rfl, rfl, retEq, rfl, rfl, rfl, rfl,
        valid, cut, nonzero, run, rfl, rfl, checked, pop, domain⟩
      cases retEq
      dsimp only [budgets]
      rw [returning_continuation_budget n originalNames retHandler originalL1 originalL2
        dest args handler source xs args1 prog ss envs ⟨get, bad, find, valid, cut⟩ nonzero
        x ys s2 s1 run checked pop domain]
      exact child
    · intro xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2
        envs v5 s2 v8 x y v n' v2 h v4 handlerL1 handlerL2 facts
      have child := ih.2.1 xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11
        originalL1 originalL2 envs v5 s2 v8 x y v n' v2 h v4 handlerL1 handlerL2 facts
      rcases facts with ⟨get, bad, find, rfl, rfl, retEq, rfl, rfl, rfl, rfl,
        valid, cut, nonzero, run, rfl, rfl, handlerEq, rfl, rfl, rfl, checked, domain⟩
      cases retEq
      cases handlerEq
      dsimp only [budgets]
      rw [exception_continuation_budget n originalNames retHandler originalL1 originalL2
        dest args n' handlerL1 handlerL2 h source xs args1 prog ss envs
        ⟨get, bad, find, valid, cut⟩ nonzero x y s2 run (by intro neq; exact neq checked) domain]
      exact child
    · intro xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs facts
      have child := ih.2.2.1 xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11
        originalL1 originalL2 envs facts
      rcases facts with ⟨get, bad, find, rfl, rfl, retEq, rfl, rfl, rfl, rfl, valid, cut, nonzero⟩
      cases retEq
      dsimp only [budgets]
      rw [returning_callee_budget n originalNames retHandler originalL1 originalL2
        dest args handler source xs args1 prog ss envs ⟨get, bad, find, valid, cut⟩ nonzero]
      exact child
    · intro xs v3 args1 v10 prog ss facts
      have child := ih.2.2.2 xs v3 args1 v10 prog ss facts
      rcases facts with ⟨get, bad, find, rfl, rfl, retEq, handlerEq, nonzero⟩
      cases retEq
      cases handlerEq
      dsimp only [budgets]
      rw [tail_call_budgets dest args source xs args1 prog ss get bad find nonzero]
      exact child
  exact (Call.compCorrectCall budgets.1 budgets.2.1 budgets.2.2 ac ret dest args handler source localIH).mono
    (callWorkBudgets_funded ret dest args handler source)

#print axioms wordWork_call_correct
end InitECandidate.Runtime.WordToStack
