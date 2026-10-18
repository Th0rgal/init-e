import InitECandidate.Runtime.WordPathWorkControl
import InitECandidate.Runtime.WordCodeSize
import InitECandidate.Runtime.WorkCeiling
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Selected-path Word work is affine in the source clock actually consumed,
with a syntax-size potential for the current program. -/
def WordAffine {width : Nat} [NeZero width] {C F : Type} (rate : Nat)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ result post, evaluate p s = (result, post) →
    wordPathWork p s ≤ rate * (s.clock - post.clock) + 2 * sizeOf p

abbrev WordAffineIH {width : Nat} [NeZero width] {C F : Type} (limit : Nat)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ child (next : WordSemStateFiniteExact width C F),
    workRank limit next.clock (sizeOf child) < workRank limit s.clock (sizeOf p) →
    sizeOf child ≤ limit → WordCodeSize limit next → noInstallSubprogsHOL child = true →
    WordAffine (2 * limit + 2) child next

theorem word_prog_size_positive {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) :
    0 < sizeOf p := by
  cases p <;> simp_wf <;> omega

theorem wordPath_seq_affine {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (a b : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (small : sizeOf (.seq a b : WordLangProgHOL (BitVec width)) ≤ limit)
    (bounded : WordCodeSize limit s) (safe : noInstallSubprogsHOL (.seq a b) = true)
    (ih : WordAffineIH limit (.seq a b) s) : WordAffine (2 * limit + 2) (.seq a b) s := by
  have sa : sizeOf a < sizeOf (.seq a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
  have sb : sizeOf b < sizeOf (.seq a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
  have total : 1 + sizeOf a + sizeOf b ≤ sizeOf (.seq a b : WordLangProgHOL (BitVec width)) := by
    simp_wf <;> omega
  have parts : noInstallSubprogsHOL a = true ∧ noInstallSubprogsHOL b = true := by
    simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using safe
  have first := ih a s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) sa) (by omega) bounded parts.1
  intro result post run
  rw [wordPathWork_seq]
  cases ra : evaluate a s with
  | mk r1 middle =>
    have c1 := (evaluate_clock a s r1 middle ra).1
    have fb := first r1 middle ra
    have middleBound : WordCodeSize limit middle := by
      have next := bounded.evaluated a parts.1
      rwa [fix_clock_evaluate, ra] at next
    rw [WordSemStateFiniteExact.evaluate, fix_clock_evaluate, ra] at run
    cases r1 with
    | none =>
      dsimp only at run ⊢
      have second := ih b middle (workRank_subprogram _ _ _ _ _ c1 sb) (by omega) middleBound parts.2
        result post run
      have c2 := (evaluate_clock b middle result post run).1
      have split : s.clock - post.clock = (s.clock - middle.clock) + (middle.clock - post.clock) := by omega
      rw [split, Nat.mul_add]
      omega
    | some value =>
      dsimp only at run ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      omega

theorem wordPath_if_affine {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (cmp : Compiler.Encoders.Asm.HolCmp) (reg : Nat)
    (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (small : sizeOf (.ite cmp reg ri a b : WordLangProgHOL (BitVec width)) ≤ limit)
    (bounded : WordCodeSize limit s) (safe : noInstallSubprogsHOL (.ite cmp reg ri a b) = true)
    (ih : WordAffineIH limit (.ite cmp reg ri a b) s) : WordAffine (2 * limit + 2) (.ite cmp reg ri a b) s := by
  have sa : sizeOf a < sizeOf (.ite cmp reg ri a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
  have sb : sizeOf b < sizeOf (.ite cmp reg ri a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
  have parts : noInstallSubprogsHOL a = true ∧ noInstallSubprogsHOL b = true := by
    simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using safe
  have first := ih a s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) sa) (by omega) bounded parts.1
  have second := ih b s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) sb) (by omega) bounded parts.2
  intro result post run
  rw [WordSemStateFiniteExact.evaluate] at run
  rw [wordPathWork]
  cases hx : getVar reg s with
  | none => simp only [hx] at run ⊢; omega
  | some x =>
    cases hy : getVarImm ri s with
    | none => simp only [hx, hy] at run ⊢; omega
    | some y =>
      cases hc : wordSemWordCmp cmp x y with
      | none => simp only [hx, hy, hc] at run ⊢; omega
      | some branch =>
        cases branch with
        | true =>
          simp only [hx, hy, hc] at run ⊢
          have bound := first result post run
          omega
        | false =>
          simp only [hx, hy, hc] at run ⊢
          have bound := second result post run
          omega

#print axioms wordPath_seq_affine
#print axioms wordPath_if_affine
end InitECandidate.Runtime.WordToStack
