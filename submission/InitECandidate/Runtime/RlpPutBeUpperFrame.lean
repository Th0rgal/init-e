import InitECandidate.Runtime.ByteStoreUpperFence
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop} {DF : Nat}
/-- The original bounded big-endian writer preserves all words at or above dst+8. -/
theorem putBe_upper_win (hF : Fence D DF)
    (Dst N : BitVec 64) (hfit : Dst.toNat + 8 < 2 ^ 64) (hN : N.toNat ≤ 8)
    (above : Dst.toNat + 8 ≤ w.toNat) :
    AQGD D B A w Vn (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "n") = some (.val (.word N))) (fun _ _ _ => False)
      (fun _ _ _ => N.toNat = 0 ∨ Dst.toNat + N.toNat ≤ DF + 8) putBeBody := by
  unfold putBeBody
  let LI := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
    ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ N.toNat ∧
      (I.toNat < N.toNat → Dst.toNat + N.toNat ≤ DF + 8)
  refine r_dec (LB := LI) (LQ' := fun _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ ⟨hd,hn⟩ ev
    simp [EV,evalHOLExact,hn] at ev; subst ev
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,N,lookup_update_eq' _ _ _,le_refl _,fun h => absurd h (by omega)⟩
  refine aqgd_seq (Q := fun L _ _ => LI L ∧ L.lookup (ofString "i") = some (.val (.word 0)))
    (aqgd_whileE (I := fun L _ _ => LI L)
      (C := fun L _ _ => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ 0 < I.toNat)
      (E := fun L _ _ => L.lookup (ofString "i") = some (.val (.word 0))) (Qb := fun _ _ _ => False) _ ?_ ?_
      (aqgb_of_aqgd ?_) |> fun h => aqgd_conseq h (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h))
    (aqgd_return _ ?_)
  · intro F s x _ _ ⟨_,I,hi,_⟩ _ ev nz
    simp [EV,evalHOLExact,hi,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨I,hi,?_⟩
    by_cases h : (0#64 : BitVec 64) < I
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s x _ _ ⟨_,I,hi,_⟩ _ ev z
    simp [EV,evalHOLExact,hi,Compiler.Encoders.Asm.wordCmpHOL] at ev
    have e : I = 0#64 := by
      by_cases h : (0#64 : BitVec 64) < I
      · simp [h] at ev; subst z; exact absurd ev (by decide)
      · apply BitVec.eq_of_toNat_eq; simp [BitVec.lt_def] at h; simpa using h
    rw [e] at hi; exact hi
  · -- loop body: i = i - 1; st8 dst + i, v; v = v >>> 8
    let LJ := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
      ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < N.toNat ∧
        (I.toNat + 1 < N.toNat → Dst.toNat + N.toNat ≤ DF + 8)
    refine aqgd_seq (r_assign (LQ := LJ) _ _ ?_) (aqgd_seq (r_stb_below (LP := LJ) (LQ := LI) _ _ ?_)
      (r_assign _ _ ?_))
    · intro F s v _ ⟨⟨hd,I,hi,hle,hb⟩,I',hi',pos⟩ ev
      rw [hi] at hi'; simp at hi'; subst hi'
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
      have e1 : (I - 1).toNat = I.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
      exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,I - 1,lookup_update_eq' _ _ _,by omega,
        fun h => hb (by omega)⟩
    · intro F s _ ⟨hd,I,hi,hlt,hb⟩
      refine ⟨Dst + I,by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord],?_,?_⟩
      · have : (Dst + I).toNat = Dst.toNat + I.toNat := by simp [BitVec.toNat_add]; omega
        omega
      · intro hD
        have hb8 := fence_byte hF hD
        have : (Dst + I).toNat = Dst.toNat + I.toNat := by simp [BitVec.toNat_add]; omega
        exact ⟨hd,I,hi,by omega,fun _ => by
          by_cases h : I.toNat + 1 < N.toNat
          · exact hb h
          · omega⟩
    · intro F s v _ ⟨hd,I,hi,hle,hb⟩ _
      exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,I,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hi,hle,hb⟩
  · intro F s v _ _ _ ⟨⟨_,I,hi,hle,hb⟩,hz⟩ _ _
    rw [hi] at hz; simp at hz; subst hz
    by_cases h : N.toNat = 0
    · exact Or.inl h
    · exact Or.inr (hb (by simp; omega))

#print axioms putBe_upper_win
end
end InitECandidate.Runtime
