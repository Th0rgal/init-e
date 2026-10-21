import InitECandidate.Runtime.LoopWordPLSiteTab
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Kernel-computable copies of `compHOL`'s label threading and of the
`SiteLe` walk, for site-charge certificates on the pinned Loop bodies. -/

/-- Structural label threading of `LoopToWord.compHOL`. -/
def labAfterS : HolLoopProg 64 → Nat × Nat → Nat × Nat
  | .seq a b, l => labAfterS b (labAfterS a l)
  | .ite _ _ _ y n _, l => labAfterS n (labAfterS y l)
  | .loop _ b _, l => labAfterS b l
  | .mark b, l => labAfterS b l
  | .call (some _) _ _ none, l => (l.1, l.2 + 1)
  | .call (some _) _ _ (some (_, p1, p2, _)), l =>
      let l2 := labAfterS p2 (labAfterS p1 (l.1, l.2 + 1))
      (l2.1, l2.2 + 1)
  | _, l => l

theorem labAfterS_eq : ∀ (p : HolLoopProg 64) (l : Nat × Nat), labAfterS p l = labAfter p l
  | .seq a b, l => by
    show labAfterS b (labAfterS a l) = _
    rw [labAfterS_eq a, labAfterS_eq b]; unfold labAfter
    conv => rhs; rw [LoopToWord.compHOL.eq_def]
  | .ite op r ri y n live, l => by
    show labAfterS n (labAfterS y l) = _
    rw [labAfterS_eq y, labAfterS_eq n]; unfold labAfter
    conv => rhs; rw [LoopToWord.compHOL.eq_def]
  | .loop li b lo, l => by
    show labAfterS b l = _
    rw [labAfterS_eq b]; unfold labAfter
    conv => rhs; rw [LoopToWord.compHOL.eq_def]
  | .mark b, l => by
    show labAfterS b l = _
    rw [labAfterS_eq b]; unfold labAfter
    conv => rhs; rw [LoopToWord.compHOL.eq_def]
  | .call (some r) t a none, l => by
    show (l.1, l.2 + 1) = _
    unfold labAfter; rw [LoopToWord.compHOL.eq_def]
  | .call (some (names, live)) t args (some (n, p1, p2, lo)), l => by
    show ((labAfterS p2 (labAfterS p1 (l.1, l.2 + 1))).1, (labAfterS p2 (labAfterS p1 (l.1, l.2 + 1))).2 + 1) = _
    rw [labAfterS_eq p1, labAfterS_eq p2]; unfold labAfter
    conv => rhs; rw [LoopToWord.compHOL.eq_def]
  | .primitive ds op as, l => by
    show l = _; unfold labAfter; rw [LoopToWord.compHOL.eq_def]; dsimp only; split <;> rfl
  | .arith op, l => by
    show l = _; unfold labAfter; rw [LoopToWord.compHOL.eq_def]; cases op <;> rfl
  | .call none t a h, l | .skip, l | .assign _ _, l | .store _ _, l | .setGlobal _ _, l | .load32 _ _, l
  | .loadByte _ _, l | .store32 _ _, l | .storeByte _ _, l | .break _, l | .continue _, l | .raise _, l
  | .return _, l | .shMem _ _ _, l | .tick, l | .fail, l | .locValue _ _, l | .ffi _ _ _ _ _ _, l => by
    show l = _; unfold labAfter; rw [LoopToWord.compHOL.eq_def]

#print axioms labAfterS_eq
/-- Kernel-computable `SiteLe`, single pass: the label after `p` if every
returning call passes, `none` otherwise. -/
def siteW (A B : Nat × Nat → Option Nat → Nat) : Nat × Nat → HolLoopProg 64 → Option (Nat × Nat)
  | l, .mark p => siteW A B l p
  | l, .seq a b => match siteW A B l a with
    | some l1 => siteW A B l1 b
    | none => none
  | l, .ite _ _ _ y n _ => match siteW A B l y with
    | some l1 => siteW A B l1 n
    | none => none
  | l, .loop _ b _ => siteW A B l b
  | l, .call (some _) t _ none => if A l t ≤ B l t then some (l.1, l.2 + 1) else none
  | l, .call (some _) t _ (some (_, hp, cont, _)) =>
      if A l t ≤ B l t then
        match siteW A B (l.1, l.2 + 1) hp with
        | some l1 => match siteW A B l1 cont with
          | some l2 => some (l2.1, l2.2 + 1)
          | none => none
        | none => none
      else none
  | l, _ => some l

theorem siteW_sound (A B : Nat × Nat → Option Nat → Nat) :
    ∀ (l : Nat × Nat) (p : HolLoopProg 64) (l' : Nat × Nat), siteW A B l p = some l' →
      SiteLe A B l p ∧ labAfterS p l = l'
  | l, .mark p, l', h => by
    simp only [siteW] at h; obtain ⟨h1, h2⟩ := siteW_sound A B l p l' h
    exact ⟨by simpa only [SiteLe] using h1, by simpa only [labAfterS] using h2⟩
  | l, .seq a b, l', h => by
    simp only [siteW] at h
    split at h
    · rename_i l1 ha
      obtain ⟨sa, la⟩ := siteW_sound A B l a l1 ha
      obtain ⟨sb, lb⟩ := siteW_sound A B l1 b l' h
      refine ⟨⟨sa, ?_⟩, ?_⟩
      · rw [← labAfterS_eq, la]; exact sb
      · simp only [labAfterS, la, lb]
    · cases h
  | l, .ite op r ri y n live, l', h => by
    simp only [siteW] at h
    split at h
    · rename_i l1 hy
      obtain ⟨sy, ly⟩ := siteW_sound A B l y l1 hy
      obtain ⟨sn, ln⟩ := siteW_sound A B l1 n l' h
      refine ⟨⟨sy, ?_⟩, ?_⟩
      · rw [← labAfterS_eq, ly]; exact sn
      · simp only [labAfterS, ly, ln]
    · cases h
  | l, .loop li b lo, l', h => by
    simp only [siteW] at h; obtain ⟨h1, h2⟩ := siteW_sound A B l b l' h
    exact ⟨by simpa only [SiteLe] using h1, by simpa only [labAfterS] using h2⟩
  | l, .call (some r) t a none, l', h => by
    simp only [siteW] at h
    split at h
    · cases h; exact ⟨⟨by assumption, trivial⟩, rfl⟩
    · cases h
  | l, .call (some r) t a (some (n, hp, cont, lo)), l', h => by
    simp only [siteW] at h
    split at h
    · rename_i hle
      split at h
      · rename_i l1 hh
        split at h
        · rename_i l2 hc
          cases h
          obtain ⟨sh, lh⟩ := siteW_sound A B _ hp l1 hh
          obtain ⟨sc, lc⟩ := siteW_sound A B l1 cont l2 hc
          refine ⟨⟨hle, sh, ?_⟩, ?_⟩
          · rw [← labAfterS_eq, lh]; exact sc
          · simp only [labAfterS, lh, lc]
        · cases h
      · cases h
    · cases h
  | l, .call none t a h', l', h | l, .skip, l', h | l, .assign _ _, l', h | l, .store _ _, l', h
  | l, .setGlobal _ _, l', h | l, .load32 _ _, l', h | l, .loadByte _ _, l', h | l, .store32 _ _, l', h
  | l, .storeByte _ _, l', h | l, .break _, l', h | l, .continue _, l', h | l, .raise _, l', h
  | l, .return _, l', h | l, .shMem _ _ _, l', h | l, .tick, l', h | l, .fail, l', h
  | l, .locValue _ _, l', h | l, .ffi _ _ _ _ _ _, l', h | l, .primitive _ _ _, l', h | l, .arith _, l', h => by
    simp only [siteW, Option.some.injEq] at h; subst h; exact ⟨by simp [SiteLe], rfl⟩

#print axioms siteW_sound
end InitECandidate.Runtime.FineCost
