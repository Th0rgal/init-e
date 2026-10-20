import InitECandidate.Runtime.PtBalRmChgGD
/-!
The storage-write part of an account record: the slot table `t0` (ready, values the live storage-write lists `Ls`)
and its lists. Two updates: an existing list `l ∈ Ls` changed with fresh growth (`adO_stOld`), and a fresh list `l`
added to the table, the table possibly relocated into fresh heap (`adO_stNew`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Regions after adding the list `l` (region `R`) with the table region now `Rt`. -/
def rgNew (Rg : AdC → BitVec 64 → Prop) (Rt R : BitVec 64 → Prop) (l : BitVec 64) : AdC → BitVec 64 → Prop
  | .t0 => Rt
  | .lst l' => if l' = l then R else Rg (.lst l')
  | c => Rg c

/-- A component of the new regions: the table, the new list, or an old live one. -/
theorem rgNew_cases {Rg : AdC → BitVec 64 → Prop} {Rt R : BitVec 64 → Prop} {l : BitVec 64} {Ls : Set (BitVec 64)}
    {c : AdC} {x : BitVec 64} (hc : AdC.live (insert l Ls) c) (hx : rgNew Rg Rt R l c x) :
    (c = .t0 ∧ Rt x) ∨ (c = .lst l ∧ R x) ∨ (AdC.live Ls c ∧ c ≠ .t0 ∧ c ≠ .lst l ∧ Rg c x) := by
  cases c with
  | t0 => exact Or.inl ⟨rfl,hx⟩
  | lst l' =>
    by_cases e : l' = l
    · subst e; simp only [rgNew,if_pos rfl] at hx; exact Or.inr (Or.inl ⟨rfl,hx⟩)
    · simp only [rgNew,if_neg e] at hx
      have : l' ∈ Ls := by
        simp only [AdC.live,Set.mem_insert_iff] at hc; exact hc.resolve_left e
      exact Or.inr (Or.inr ⟨this,by simp,by simp [e],hx⟩)
  | recw => exact Or.inr (Or.inr ⟨trivial,by simp,by simp,hx⟩)
  | t8 => exact Or.inr (Or.inr ⟨trivial,by simp,by simp,hx⟩)
  | l16 => exact Or.inr (Or.inr ⟨trivial,by simp,by simp,hx⟩)
  | l24 => exact Or.inr (Or.inr ⟨trivial,by simp,by simp,hx⟩)
  | l32 => exact Or.inr (Or.inr ⟨trivial,by simp,by simp,hx⟩)

#print axioms rgNew_cases

section ad
variable {D : BitVec 64 → Prop} {B : Bool} {O : BitVec 64 → Prop} {ad H : BitVec 64} {M : Mem}

/-- An existing storage-write list changed (grown into fresh heap); everything else of the record by frame. -/
theorem adO_stOld {Ls : Set (BitVec 64)} {Rg : AdC → BitVec 64 → Prop}
    {t0 t8 l16 l24 l32 : BitVec 64} {l0 : TLay} {Hl0 : BitVec 64}
    (cells : M ad = .word t0 ∧ M (ad + 8#64) = .word t8 ∧ M (ad + 16#64) = .word l16 ∧
      M (ad + 24#64) = .word l24 ∧ M (ad + 32#64) = .word l32) (hrw : ∀ x, RecW ad x → Rg .recw x)
    (tr : TabRV D B t0 l0 Hl0 Ls M ∧ Hl0.toNat ≤ H.toNat ∧ l0.KL = 32#64 ∧ l0.SD.toNat ≤ 56 ∧
      ∀ x, TabPhys t0 l0 x → Rg .t0 x)
    (tO : TabO (Rg .t8) t8 H M) (a : LstO 40#64 (Rg .l16) l16 M) (b : LstO 16#64 (Rg .l24) l24 M)
    (c : LstO 24#64 (Rg .l32) l32 M) (ls : ∀ l ∈ Ls, LstO 40#64 (Rg (.lst l)) l M) (dis : RgDis (AdC.live Ls) Rg)
    (inO : ∀ c, AdC.live Ls c → ∀ x, Rg c x → O x)
    (l : BitVec 64) (hl : l ∈ Ls) (M' : Mem) (H' : BitVec 64) (le : H.toNat ≤ H'.toNat)
    (lo : LstO 40#64 (fun x => Rg (.lst l) x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) l M')
    (fr : ∀ x, x.toNat < H.toNat → ¬ Rg (.lst l) x → M' x = M x) (hO : ∀ x, O x → x.toNat < H.toNat) :
    AdO D B (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ad H' M' := by
  obtain ⟨c0,c8,c16,c24,c32⟩ := cells
  obtain ⟨rv,hl0,kl,sd,ph⟩ := tr
  have k : ∀ cc, AdC.live Ls cc → cc ≠ .lst l → ∀ x, Rg cc x → M' x = M x := fun cc hc ne x hx =>
    fr x (hO x (inO cc hc x hx)) (fun h => dis cc (.lst l) hc hl ne x hx h)
  have kr : ∀ x, RecW ad x → M' x = M x := fun x hx => k .recw trivial (by simp) x (hrw x hx)
  refine ⟨t0,t8,l16,l24,l32,Ls,fun cc x => Rg cc x ∨ (cc = .lst l ∧ H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat),l0,Hl0,
    ⟨?_,?_,?_,?_,?_⟩,fun x hx => Or.inl (hrw x hx),
    ⟨tabRV_frame rv (fun x hx => k .t0 trivial (by simp) x (ph x hx)),by omega,kl,sd,fun x hx => Or.inl (ph x hx)⟩,
    tabO_sub (tabO_mono (tabO_frame tO (k .t8 trivial (by simp))) le) (fun x h => Or.inl h),
    lstO_sub (lstO_frame a (k .l16 trivial (by simp))) (fun x h => Or.inl h),
    lstO_sub (lstO_frame b (k .l24 trivial (by simp))) (fun x h => Or.inl h),
    lstO_sub (lstO_frame c (k .l32 trivial (by simp))) (fun x h => Or.inl h),
    fun l' hl' => ?_,fun c1 c2 h1 h2 ne x hx1 hx2 => ?_,fun cc hc x hx => ?_⟩
  · rw [kr _ (Or.inl rfl)]; exact c0
  · rw [kr _ (Or.inr (Or.inl rfl))]; exact c8
  · rw [kr _ (Or.inr (Or.inr (Or.inl rfl)))]; exact c16
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact c24
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact c32
  · by_cases e : l' = l
    · subst e
      exact lstO_sub lo (fun x h => by
        rcases h with h | ⟨h1,h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl,h1,h2⟩)
    · exact lstO_sub (lstO_frame (ls l' hl') (k (.lst l') hl' (by simp [e]))) (fun x h => Or.inl h)
  · rcases hx1 with g1 | ⟨e1,a1,_⟩ <;> rcases hx2 with g2 | ⟨e2,a2,_⟩
    · exact dis c1 c2 h1 h2 ne x g1 g2
    · have := hO x (inO c1 h1 x g1); omega
    · have := hO x (inO c2 h2 x g2); omega
    · exact ne (e1.trans e2.symm)
  · rcases hx with g | ⟨_,a1,b1⟩
    · exact Or.inl (inO cc hc x g)
    · exact Or.inr ⟨a1,b1⟩

#print axioms adO_stOld

/-- A fresh list `l` (region `R` in fresh heap) added to the slot table, the table now in `Rt` (old table region or
fresh heap, off `R`); everything else of the record by frame. -/
theorem adO_stNew {Ls : Set (BitVec 64)} {Rg : AdC → BitVec 64 → Prop}
    {t0 t8 l16 l24 l32 : BitVec 64}
    (cells : M ad = .word t0 ∧ M (ad + 8#64) = .word t8 ∧ M (ad + 16#64) = .word l16 ∧
      M (ad + 24#64) = .word l24 ∧ M (ad + 32#64) = .word l32) (hrw : ∀ x, RecW ad x → Rg .recw x)
    (tO : TabO (Rg .t8) t8 H M) (a : LstO 40#64 (Rg .l16) l16 M) (b : LstO 16#64 (Rg .l24) l24 M)
    (c : LstO 24#64 (Rg .l32) l32 M) (ls : ∀ l ∈ Ls, LstO 40#64 (Rg (.lst l)) l M) (dis : RgDis (AdC.live Ls) Rg)
    (inO : ∀ c, AdC.live Ls c → ∀ x, Rg c x → O x)
    (M' : Mem) (H' l : BitVec 64) (Rt R : BitVec 64 → Prop) (l0' : TLay) (Hl0' : BitVec 64)
    (le : H.toNat ≤ H'.toNat) (rv : TabRV D B t0 l0' Hl0' (insert l Ls) M') (hl0 : Hl0'.toNat ≤ H'.toNat)
    (kl : l0'.KL = 32#64) (sd : l0'.SD.toNat ≤ 56) (ph : ∀ x, TabPhys t0 l0' x → Rt x)
    (hRt : ∀ x, Rt x → Rg .t0 x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (lo : LstO 40#64 R l M') (hR : ∀ x, R x → H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat) (dRt : ∀ x, Rt x → ¬ R x)
    (fr : ∀ x, x.toNat < H.toNat → ¬ Rg .t0 x → M' x = M x) (hO : ∀ x, O x → x.toNat < H.toNat) :
    AdO D B (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ad H' M' := by
  obtain ⟨c0,c8,c16,c24,c32⟩ := cells
  have k : ∀ cc, AdC.live Ls cc → cc ≠ .t0 → ∀ x, Rg cc x → M' x = M x := fun cc hc ne x hx =>
    fr x (hO x (inO cc hc x hx)) (fun h => dis cc .t0 hc trivial ne x hx h)
  have kr : ∀ x, RecW ad x → M' x = M x := fun x hx => k .recw trivial (by simp) x (hrw x hx)
  have lH : H.toNat ≤ l.toNat := (hR l (by obtain ⟨_,_,_,_,_,_,_,hh,_⟩ := lo; exact hh l (Or.inl rfl))).1
  have nl : l ∉ Ls := fun hl => by
    obtain ⟨_,_,_,_,_,_,_,hh,_⟩ := ls l hl
    have := hO l (inO (.lst l) hl l (hh l (Or.inl rfl))); omega
  refine ⟨t0,t8,l16,l24,l32,insert l Ls,rgNew Rg Rt R l,l0',Hl0',⟨?_,?_,?_,?_,?_⟩,fun x hx => hrw x hx,
    ⟨rv,hl0,kl,sd,ph⟩,
    tabO_mono (tabO_frame tO (k .t8 trivial (by simp))) le,
    lstO_frame a (k .l16 trivial (by simp)),lstO_frame b (k .l24 trivial (by simp)),
    lstO_frame c (k .l32 trivial (by simp)),fun l' hl' => ?_,fun c1 c2 h1 h2 ne x hx1 hx2 => ?_,
    fun cc hc x hx => ?_⟩
  · rw [kr _ (Or.inl rfl)]; exact c0
  · rw [kr _ (Or.inr (Or.inl rfl))]; exact c8
  · rw [kr _ (Or.inr (Or.inr (Or.inl rfl)))]; exact c16
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact c24
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact c32
  · by_cases e : l' = l
    · subst e; simp only [rgNew]; exact lo
    · simp only [rgNew,if_neg e]
      have : l' ∈ Ls := by simp only [Set.mem_insert_iff] at hl'; exact hl'.resolve_left e
      exact lstO_frame (ls l' this) (k (.lst l') this (by simp))
  · have old : ∀ cc, AdC.live Ls cc → Rg cc x → x.toNat < H.toNat := fun cc hc g => hO x (inO cc hc x g)
    rcases rgNew_cases h1 hx1 with ⟨e1,r1⟩ | ⟨e1,r1⟩ | ⟨l1,n1,_,g1⟩ <;>
      rcases rgNew_cases h2 hx2 with ⟨e2,r2⟩ | ⟨e2,r2⟩ | ⟨l2,n2,_,g2⟩
    · exact ne (e1.trans e2.symm)
    · exact dRt x r1 r2
    · rcases hRt x r1 with g | ⟨a1,_⟩
      · exact dis c2 .t0 l2 trivial n2 x g2 g
      · have := old c2 l2 g2; omega
    · exact dRt x r2 r1
    · exact ne (e1.trans e2.symm)
    · have := old c2 l2 g2; have := hR x r1; omega
    · rcases hRt x r2 with g | ⟨a1,_⟩
      · exact dis c1 .t0 l1 trivial n1 x g1 g
      · have := old c1 l1 g1; omega
    · have := old c1 l1 g1; have := hR x r2; omega
    · exact dis c1 c2 l1 l2 ne x g1 g2
  · rcases rgNew_cases hc hx with ⟨_,r⟩ | ⟨_,r⟩ | ⟨l1,_,_,g⟩
    · rcases hRt x r with g | g
      · exact Or.inl (inO .t0 trivial x g)
      · exact Or.inr g
    · exact Or.inr (hR x r)
    · exact Or.inl (inO cc l1 x g)

#print axioms adO_stNew
end ad
end InitECandidate.Runtime
