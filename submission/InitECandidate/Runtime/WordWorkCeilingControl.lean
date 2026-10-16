import InitECandidate.Runtime.WordCodeSize
import InitECandidate.Runtime.WorkCeiling
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

abbrev WordCeilingIH {width : Nat} [NeZero width] {C F : Type} (limit : Nat)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ child (next : WordSemStateFiniteExact width C F),
    workRank limit next.clock (sizeOf child) < workRank limit s.clock (sizeOf p) →
    sizeOf child ≤ limit → WordCodeSize limit next → noInstallSubprogsHOL child = true →
    wordWork child next ≤ 8 ^ workRank limit s.clock (sizeOf p)

/-- Sequence work includes its second branch only at an actual normal return. -/
theorem wordWork_seq_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (a b : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (small : sizeOf (.seq a b : WordLangProgHOL (BitVec width)) ≤ limit)
    (bounded : WordCodeSize limit s) (safe : noInstallSubprogsHOL (.seq a b) = true)
    (ih : WordCeilingIH limit (.seq a b) s) :
    wordWork (.seq a b) s ≤ workCeiling limit s.clock (sizeOf (.seq a b : WordLangProgHOL (BitVec width))) := by
  have sa : sizeOf a < sizeOf (.seq a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
  have sb : sizeOf b < sizeOf (.seq a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
  have parts : noInstallSubprogsHOL a = true ∧ noInstallSubprogsHOL b = true := by
    simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using safe
  have first := ih a s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) sa) (by omega) bounded parts.1
  rw [wordWork]
  split
  rename_i result middle execution
  have lower := fixClock_IMP_LESS_EQ _ _ _ _ execution
  have middleBound := bounded.evaluated a parts.1
  rw [execution] at middleBound
  have second := ih b middle (workRank_subprogram _ _ _ _ _ lower.1 sb)
    (by omega) middleBound parts.2
  cases result
  · change 1 + wordWork a s + wordWork b middle ≤ _
    exact Nat.le_trans (by omega) (workCeiling_two _ _ _ first second)
  · change 1 + wordWork a s + 0 ≤ _
    exact Nat.le_trans (by omega) (workCeiling_one _ _ first)

/-- A conditional's conservative budget bounds both syntactic alternatives. -/
theorem wordWork_if_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (cmp : Compiler.Encoders.Asm.HolCmp) (reg : Nat)
    (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (small : sizeOf (.ite cmp reg ri a b : WordLangProgHOL (BitVec width)) ≤ limit)
    (bounded : WordCodeSize limit s) (safe : noInstallSubprogsHOL (.ite cmp reg ri a b) = true)
    (ih : WordCeilingIH limit (.ite cmp reg ri a b) s) :
    wordWork (.ite cmp reg ri a b) s ≤ workCeiling limit s.clock (sizeOf (.ite cmp reg ri a b : WordLangProgHOL (BitVec width))) := by
  have sa : sizeOf a < sizeOf (.ite cmp reg ri a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
  have sb : sizeOf b < sizeOf (.ite cmp reg ri a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
  have parts : noInstallSubprogsHOL a = true ∧ noInstallSubprogsHOL b = true := by
    simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using safe
  have first := ih a s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) sa) (by omega) bounded parts.1
  have second := ih b s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) sb) (by omega) bounded parts.2
  rw [wordWork]
  have bound := workCeiling_two _ _ _ first second
  unfold workCeiling
  omega

#print axioms wordWork_seq_ceiling
#print axioms wordWork_if_ceiling
end InitECandidate.Runtime.WordToStack
