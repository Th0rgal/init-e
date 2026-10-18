import InitECandidate.Runtime.StackRemovePathAffine
namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open StackToLab

theorem exists_least_nat {P : Nat → Prop} (h : ∃ n, P n) : ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hmin : ∀ k, P k → n ≤ k
    · exact ⟨n, hn, hmin⟩
    · have smaller : ∃ k, P k ∧ k < n := by
        apply Classical.byContradiction
        intro none
        apply hmin
        intro k pk
        apply Nat.le_of_not_lt
        intro lt
        exact none ⟨k, pk, lt⟩
      obtain ⟨k, pk, lt⟩ := smaller
      exact ih k lt pk

/-- Every admissible affine cap for a removal execution: code-size limit L and
bitmap scale S at the start state give S*((2L+2)*clock+2L). -/
def RemoveAffineCaps {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) (n : Nat) : Prop :=
  n = removePathWork p s ∨ ∃ limit scale, sizeOf p ≤ limit ∧ CodeSizeState limit s ∧
    BitmapBudget scale s ∧ n = scale * ((2 * limit + 2) * s.clock + 2 * limit)

/-- Removal budget equal to the best of the selected-path work and all affine caps. -/
noncomputable def removeAffineWork {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat :=
  Classical.choose (exists_least_nat (P := RemoveAffineCaps p s) ⟨_, Or.inl rfl⟩)

/-- Any admissible code/bitmap bound caps the budget, with no execution premise. -/
theorem removeAffineWork_le {width : Nat} [NeZero width] {C F : Type}
    (limit scale : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf p ≤ limit) (code : CodeSizeState limit s) (bitmap : BitmapBudget scale s) :
    removeAffineWork p s ≤ scale * ((2 * limit + 2) * s.clock + 2 * limit) :=
  (Classical.choose_spec (exists_least_nat (P := RemoveAffineCaps p s) ⟨_, Or.inl rfl⟩)).2 _
    (Or.inr ⟨limit, scale, sizeBound, code, bitmap, rfl⟩)

/-- For an actual nonerror execution, a clock bounded by selected-path work is
bounded by the combined budget. -/
theorem le_removeAffineWork {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (run : StackSemEvaluate.evaluate (p,s) = (result,post)) (notError : result ≠ some .error)
    (clock : Nat) (bound : clock ≤ removePathWork p s) : clock ≤ removeAffineWork p s := by
  have least := (Classical.choose_spec (exists_least_nat (P := RemoveAffineCaps p s) ⟨_, Or.inl rfl⟩)).1
  unfold removeAffineWork
  rcases least with equal | ⟨limit, scale, sizeBound, code, bitmap, equal⟩
  · rw [equal]; exact bound
  · rw [equal]
    exact Nat.le_trans bound
      (removePathWork_affine_fuel limit scale p s sizeBound code bitmap result post run notError)

#print axioms removeAffineWork_le
#print axioms le_removeAffineWork
end InitECandidate.Runtime.StackRemove
