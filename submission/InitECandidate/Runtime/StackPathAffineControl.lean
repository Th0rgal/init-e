import InitECandidate.Runtime.StackPathWorkCorrect
import InitECandidate.Runtime.StackCodeSize
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Amortized work is affine in consumed source clock, with a syntax-size
potential for the current procedure. This is a property to prove, not an axiom. -/
def AffinePathBound {width : Nat} [NeZero width] {C F : Type}
    (rate : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ result post, StackSemEvaluate.evaluate (p, s) = (result, post) → result ≠ some .error →
    pathWork p s ≤ rate * (s.clock - post.clock) + 2 * sizeOf p

theorem prog_size_positive {width : Nat} [NeZero width] (p : HolProg width) : 0 < sizeOf p := by
  cases p <;> simp_wf <;> omega

theorem pathWork_leaf_affine {width : Nat} [NeZero width] {C F : Type}
    (rate : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (leaf : workLeaf p = true) : AffinePathBound rate p s := by
  have cost : pathWork p s = 2 := by cases p <;> simp_all [workLeaf, pathWork]
  intro result post run notError
  rw [cost]
  have positive := prog_size_positive p
  omega

/-- Reached sequence components share the consumed clock additively, while
constructor syntax pays the constant local overhead. -/
theorem pathWork_seq_affine {width : Nat} [NeZero width] {C F : Type}
    (rate : Nat) (a b : HolProg width) (s : StackSemStateFiniteExact width C F)
    (first : AffinePathBound rate a s)
    (second : ∀ middle, StackSemEvaluate.evaluate (a, s) = (none, middle) → AffinePathBound rate b middle) :
    AffinePathBound rate (.seq a b) s := by
  intro result post run notError
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run
  cases firstRun : StackSemEvaluate.evaluate (a, s) with
  | mk firstResult middle =>
    rw [firstRun] at run
    have firstClock := StackSemEvaluateClock.evaluateClock a s firstResult middle firstRun
    cases firstResult with
    | none =>
      have firstBound := first none middle firstRun (by simp)
      have secondBound := second middle firstRun result post run notError
      have secondClock := StackSemEvaluateClock.evaluateClock b middle result post run
      have elapsed : s.clock - post.clock = (s.clock - middle.clock) + (middle.clock - post.clock) := by omega
      have syntaxBound : 2 + 2 * sizeOf a + 2 * sizeOf b ≤ 2 * sizeOf (.seq a b : HolProg width) := by
        simp_wf; omega
      rw [pathWork, StackSemEvaluateClock.fixClockEvaluate, firstRun]
      dsimp only
      rw [elapsed, Nat.mul_add]
      omega
    | some value =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have firstBound := first (some value) middle firstRun notError
      have syntaxBound : 2 + 2 * sizeOf a ≤ 2 * sizeOf (.seq a b : HolProg width) := by
        simp_wf; omega
      rw [pathWork, StackSemEvaluateClock.fixClockEvaluate, firstRun]
      dsimp only
      omega

/-- Only the selected branch contributes to the amortized clock budget. -/
theorem pathWork_if_affine {width : Nat} [NeZero width] {C F : Type}
    (rate : Nat) (cmp : Compiler.Encoders.Asm.HolCmp) (reg : Nat)
    (ri : Compiler.Encoders.Asm.HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (first : AffinePathBound rate a s) (second : AffinePathBound rate b s) :
    AffinePathBound rate (.ite cmp reg ri a b) s := by
  intro result post run notError
  have err : ∀ {bad : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, bad) = (result, post) → False :=
    fun eq => notError (Prod.mk.inj eq).1.symm
  rw [StackSemEvaluate.evaluate_ite] at run
  split at run
  swap; · exact (err run).elim
  rename_i x y hx hy
  cases comparison : wordSemWordCmp cmp x y with
  | none => rw [comparison] at run; exact (err run).elim
  | some branch =>
    rw [comparison] at run
    have selected : BranchCondition cmp reg ri s branch := ⟨x, y, hx, hy, comparison⟩
    cases branch with
    | false =>
      have bound := second result post run notError
      have syntaxBound : 2 + 2 * sizeOf b ≤ 2 * sizeOf (.ite cmp reg ri a b : HolProg width) := by
        simp_wf; omega
      rw [pathWork, selectedBranchBudget_eq cmp reg ri s _ _ false selected]
      simp only [Bool.false_eq_true, if_false]
      omega
    | true =>
      have bound := first result post run notError
      have syntaxBound : 2 + 2 * sizeOf a ≤ 2 * sizeOf (.ite cmp reg ri a b : HolProg width) := by
        simp_wf; omega
      rw [pathWork, selectedBranchBudget_eq cmp reg ri s _ _ true selected]
      simp only [if_true]
      omega

#print axioms pathWork_if_affine

#print axioms pathWork_leaf_affine
#print axioms pathWork_seq_affine
end InitECandidate.Runtime.StackToLab
