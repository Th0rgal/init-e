import InitECandidate.Runtime.WordPathWorkControl
import InitECandidate.Runtime.WordToStackIfBudget
import InitECandidate.Runtime.WordToStackSeqBudget

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Actual-state budgets compose across a source sequence; the second IH is
required only for the real successful first successor. -/
theorem wordPathWork_seq_correct {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (firstIH : BoundedSimulation ac first source (wordPathWork first source))
    (secondIH : ∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
      BoundedSimulation ac second middle (wordPathWork second middle)) :
    BoundedSimulation ac (.seq first second) source (wordPathWork (.seq first second) source) := by
  let tailBudget := match WordSemStateFiniteExact.evaluate first source with
    | (none, middle) => wordPathWork second middle
    | _ => 0
  have tailIH : ∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
      BoundedSimulation ac second middle tailBudget := by
    intro result middle facts
    obtain ⟨run, rfl⟩ := facts
    have tailEq : tailBudget = wordPathWork second middle := by
      dsimp only [tailBudget]
      rw [← run]
    rw [tailEq]
    exact secondIH none middle ⟨run, rfl⟩
  have bound : wordPathWork first source + tailBudget ≤ wordPathWork (.seq first second) source := by
    rw [wordPathWork_seq]
    dsimp only [tailBudget]
    cases run : WordSemStateFiniteExact.evaluate first source with
    | mk result middle => cases result <;> dsimp only <;> omega
  exact (Seq.compCorrectSeq (wordPathWork first source) tailBudget ac first second source
    ⟨tailIH, firstIH⟩).mono bound

def IfWorkIH_path {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ v3 v4 x y value,
    (WordSemStateFiniteExact.getVar register source,
      WordSemStateFiniteExact.getVarImm operand source) = (v3, v4) ∧
    v3 = some x ∧ v4 = some y ∧ wordSemWordCmp comparison x y = some value ∧
    value = true → BoundedSimulation ac first source (wordPathWork first source)) ∧
  (∀ v3 v4 x y value,
    (WordSemStateFiniteExact.getVar register source,
      WordSemStateFiniteExact.getVarImm operand source) = (v3, v4) ∧
    v3 = some x ∧ v4 = some y ∧ wordSemWordCmp comparison x y = some value ∧
    ¬ value = true → BoundedSimulation ac second source (wordPathWork second source))


/-- Both literal selected-branch guards retain their own actual-state budget. -/
theorem wordPathWork_if_correct {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width)) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : IfWorkIH_path ac comparison register operand first second source) :
    BoundedSimulation ac (.ite comparison register operand first second) source
      (wordPathWork (.ite comparison register operand first second) source) := by
  apply If.compCorrectIf _ ac comparison register operand first second source
  constructor
  · intro v3 v4 x y value guards
    obtain ⟨pair, hx, hy, compared, isTrue⟩ := guards
    obtain ⟨e3, e4⟩ := Prod.mk.inj pair
    subst isTrue
    exact (ih.1 v3 v4 x y true ⟨pair, hx, hy, compared, rfl⟩).mono
      (if_first_work_le_path comparison register operand first second source x y (e3.trans hx) (e4.trans hy) compared)
  · intro v3 v4 x y value guards
    obtain ⟨pair, hx, hy, compared, notTrue⟩ := guards
    obtain ⟨e3, e4⟩ := Prod.mk.inj pair
    have isFalse : value = false := by simpa using notTrue
    subst isFalse
    exact (ih.2 v3 v4 x y false ⟨pair, hx, hy, compared, by decide⟩).mono
      (if_second_work_le_path comparison register operand first second source x y (e3.trans hx) (e4.trans hy) compared)

#print axioms wordPathWork_seq_correct
#print axioms wordPathWork_if_correct
end InitECandidate.Runtime.WordToStack
