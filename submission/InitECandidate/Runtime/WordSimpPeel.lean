import InitECandidate.Runtime.WordSimpCert
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordSimp

/-! Deep left `seq` spines: levels whose last statement does not simplify to an
`if` cannot hoist, so `SdiOk` splits there without simplifying the prefix. -/

theorem tryIfHoist1_none_of_destIf {p1 p2 : WordLangProgHOL (BitVec 64)} (h : destIf p2 = none) :
    tryIfHoist1 p1 p2 = none := by
  simp only [tryIfHoist1, h]

/-- Peel up to `k` top spine levels whose statement does not simplify to an
`if`, then check the rest with `sdiOkB`. The deeper prefix is checked first,
so the kernel forces the constant-folding state bottom-up. -/
noncomputable def peelB (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T : SiteTable) :
    Nat → WordLangProgHOL (BitVec 64) → Bool
  | k + 1, .seq p1 p2 => peelB c T k p1 && ((destIf (sdiF p2)).isNone && sdiOkB c T p2)
  | _, p => sdiOkB c T p

theorem peelB_sound (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T : SiteTable) :
    ∀ (k : Nat) (p : WordLangProgHOL (BitVec 64)), peelB c T k p = true → SdiOk c (surOf T) p
  | 0, p, h => by simp only [peelB] at h; exact sdiOkB_sound c T p h
  | k + 1, p, h => by
      cases p
      case seq p1 p2 =>
        simp only [peelB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
        obtain ⟨h1, hd, h2⟩ := h
        rw [sdiF_eq] at hd
        simp only [SdiOk, tryIfHoist1_none_of_destIf hd]
        exact ⟨peelB_sound c T k p1 h1, sdiOkB_sound c T p2 h2⟩
      all_goals (simp only [peelB] at h; exact sdiOkB_sound c T _ h)

#print axioms peelB_sound
end InitECandidate.Runtime.FineCost
