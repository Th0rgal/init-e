import InitECandidate.Runtime.PtRegRgGD
/-!
Sub-registries. A registry restricts along an injective index map `e` to the tables `e i` (`regT_restrict`, the
content table of the restriction given by its header and an explicit content fact), and a restricted registry at a later
memory and heap pointer extends back to the whole registry (`regT_extend`) when the tables outside the restriction kept
their cells, headers and arrays and the restricted tables' arrays moved only inside their old footprint, an outside
region off every cell, or the fresh heap.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem intabf_fp {Tt : BitVec 64} {l : TLay} {x : BitVec 64} (h : InTabF Tt l.KS l.SD l.C l.US l.VS l.OS l.OPS x) :
    HdrR Tt x ∨ l.arr x := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

section rs
variable {n m : Nat} {c T : Fin n → BitVec 64} {O : BitVec 64 → Prop} {D : BitVec 64 → Prop} {B : Bool}
  {ko : Fin n} {e : Fin m → Fin n}

/-- Restriction of a registry to the tables `e i`; the restriction's content table `e ko'` by an explicit content fact
for its header layout. -/
theorem regT_restrict {H : BitVec 64} {M : Mem} (inj : ∀ i j, e i = e j → i = j) {ko' : Fin m} {kA kB : Fin n}
    (hAB : kA ≠ kB) (h : RegT n c T O H M D B ko) (lz : TLay) (hz : lz.hdr M (T (e ko')))
    (pz : lz.C.toNat = 2 ^ lz.b) (tz : TCont D B M (T (e ko')) lz) :
    RegT m (fun i => c (e i)) (fun i => T (e i)) O H M D B ko' := by
  obtain ⟨l,pure,mem,_,_⟩ := h
  have hl : l (e ko') = lz := tlay_eq hz (mem (e ko')).2 pz (pure.1 _).1.pow
  refine ⟨fun i => l (e i),⟨fun i => pure.1 (e i),fun i j ne => pure.2.1 _ _ (fun h => ne (inj _ _ h)),
    fun x hx i => pure.2.2 x hx (e i)⟩,fun i => mem (e i),?_,fun x hx => regPure_arr_below pure hAB _ hx⟩
  show TCont D B M (T (e ko')) (l (e ko'))
  rw [hl]; exact tz

#print axioms regT_restrict

/-- Footprint of a table: cell, header, arrays. -/
def TFp (cc Tt : BitVec 64) (l : TLay) (x : BitVec 64) : Prop := x = cc ∨ HdrR Tt x ∨ l.arr x

/-- The old footprint of the restricted tables (registry region read off memory) is inside their old footprints. -/
theorem regRgM_sub_fp {M : Mem} {l : Fin n → TLay} (mem : RegMem n c T l M) {x : BitVec 64}
    (h : RegRgM m (fun i => c (e i)) (fun i => T (e i)) M x) : ∃ i, TFp (c (e i)) (T (e i)) (l (e i)) x := by
  obtain ⟨i,hx⟩ := h
  refine ⟨i,?_⟩
  rcases hx with h | h | ⟨KL,SD,C,N,KS,VS,US,OS,OPS,hd,ha⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨_,e1,e2,_,e4,e5,e6,e7,e8⟩ := hdr_unique hd (mem (e i)).2
    refine Or.inr (Or.inr ?_)
    show ArrOf (l (e i)).C (l (e i)).SD (l (e i)).KS (l (e i)).VS (l (e i)).US (l (e i)).OS (l (e i)).OPS x
    rw [e1,e2,e4,e5,e6,e7,e8]; exact ha

/-- Distinct tables of a registry: the footprint of `Y` is off the canonical footprint of `X` (cells included). -/
theorem fp_off_canon {H : BitVec 64} {M : Mem} {l : Fin n → TLay} (pure : RegPure n c T O H l)
    (mem : RegMem n c T l M) {jX jY : Fin n} (ne : jX ≠ jY) {x : BitVec 64} (hY : TFp (c jY) (T jY) (l jY) x) :
    ¬ (l jX).canon (T jX) H x := pure.2.1 jX jY ne x hY

/-- Distinct tables have distinct cells. -/
theorem cell_ne {H : BitVec 64} {M : Mem} {l : Fin n → TLay} (pure : RegPure n c T O H l)
    (mem : RegMem n c T l M) {jX jY : Fin n} (ne : jX ≠ jY) : c jX ≠ c jY := by
  intro hc
  have e1 := (mem jX).1
  rw [hc,(mem jY).1] at e1
  simp only [HolWordLab.word.injEq] at e1
  have fit := (pure.1 jY).1.eEnd
  exact pure.2.1 jX jY ne (T jY) (Or.inr (Or.inl ⟨le_refl _,by omega⟩))
    (Or.inl ⟨by rw [e1],by rw [e1]; omega⟩)

/-- The registry footprint read off memory of the tables outside the restriction. -/
def OthFp (c T : Fin n → BitVec 64) (M : Mem) (j : Fin n) (x : BitVec 64) : Prop :=
  x = c j ∨ HdrR (T j) x ∨ ∃ KL SD C N KS VS US OS OPS : BitVec 64, Hdr M (T j) KL SD C N KS VS US OS OPS ∧
    ArrOf C SD KS VS US OS OPS x

section ex
variable {H0 H' : BitVec 64} {M0 M : Mem} {l : Fin n → TLay} {Rr' Rx : BitVec 64 → Prop}

/-- New layout of a restricted table against an old table outside the restriction. -/
theorem sepSO {kA kB : Fin n} (hAB : kA ≠ kB) (pure : RegPure n c T O H0 l) (mem : RegMem n c T l M0)
    (le : H0.toNat ≤ H'.toNat) {lX : TLay} (rr : ∀ x, lX.arr x → Rr' x)
    (hRr : ∀ x, Rr' x → RegRgM m (fun i => c (e i)) (fun i => T (e i)) M0 x ∨ Rx x ∨
      (H0.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (hRx : ∀ x, Rx x → O x ∧ ∀ i, x ≠ c i) {i : Fin m} {j : Fin n} (hj : ∀ i, e i ≠ j) :
    TabSep (T (e i)) lX (c j) (T j) (l j) H' := by
  intro x hY hc
  have below : x.toNat < H0.toNat := by
    rcases hY with h | h | h
    · exact regPure_below pure x ⟨j,Or.inl h⟩
    · exact regPure_below pure x ⟨j,Or.inr h⟩
    · exact regPure_arr_below pure hAB j h
  rcases hc with hh | ha | hge
  · exact pure.2.1 (e i) j (hj i) x hY (Or.inl hh)
  · rcases hRr x (rr x ha) with hrg | hx | ⟨h1,_⟩
    · obtain ⟨i',hfp⟩ := regRgM_sub_fp mem hrg
      rcases hfp with hce | hh | ha2
      · rcases hY with hcj | hh | ha3
        · exact cell_ne pure mem (hj i') (hce.symm.trans hcj)
        · exact pure.2.1 j (e i') (fun h => hj i' h.symm) x (Or.inl hce) (Or.inl hh)
        · exact pure.2.1 j (e i') (fun h => hj i' h.symm) x (Or.inl hce) (Or.inr (Or.inl ha3))
      · exact pure.2.1 (e i') j (hj i') x hY (Or.inl hh)
      · exact pure.2.1 (e i') j (hj i') x hY (Or.inr (Or.inl ha2))
    · obtain ⟨ho,hne⟩ := hRx x hx
      rcases hY with hcj | hh | ha3
      · exact hne j hcj
      · exact pure.2.2 x ho j (Or.inl hh)
      · exact pure.2.2 x ho j (Or.inr (Or.inl ha3))
    · omega
  · omega

#print axioms sepSO

/-- An old table outside the restriction against the new layout of a restricted table. -/
theorem sepOS {kA kB : Fin n} (hAB : kA ≠ kB) (pure : RegPure n c T O H0 l) (mem : RegMem n c T l M0)
    (le : H0.toNat ≤ H'.toNat) {lY : TLay} (rr : ∀ x, lY.arr x → Rr' x)
    (hRr : ∀ x, Rr' x → RegRgM m (fun i => c (e i)) (fun i => T (e i)) M0 x ∨ Rx x ∨
      (H0.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (hRx : ∀ x, Rx x → O x ∧ ∀ i, x ≠ c i) {i : Fin m} {j : Fin n} (hj : ∀ i, e i ≠ j) :
    TabSep (T j) (l j) (c (e i)) (T (e i)) lY H' := by
  intro x hY hc
  have hc' := canon_mono hc le
  have ne : j ≠ e i := fun h => hj i h.symm
  rcases hY with hce | hh | ha
  · exact pure.2.1 j (e i) ne x (Or.inl hce) hc'
  · exact pure.2.1 j (e i) ne x (Or.inr (Or.inl hh)) hc'
  · rcases hRr x (rr x ha) with hrg | hx | ⟨h1,h2⟩
    · obtain ⟨i',hfp⟩ := regRgM_sub_fp mem hrg
      exact pure.2.1 j (e i') (fun h => hj i' h.symm) x hfp hc'
    · exact pure.2.2 x (hRx x hx).1 j hc'
    · rcases hc with hh | ha2 | hge
      · have := regPure_below pure x ⟨j,Or.inr hh⟩; omega
      · have := regPure_arr_below pure hAB j ha2; omega
      · omega

#print axioms sepOS
end ex

/-- Layouts of the extension: the new layouts on the restricted tables, the old ones elsewhere. -/
noncomputable def extL (e : Fin m → Fin n) (l : Fin n → TLay) (l' : Fin m → TLay) (j : Fin n) : TLay :=
  if h : ∃ i, e i = j then l' (Classical.choose h) else l j

theorem extL_sub (inj : ∀ i j, e i = e j → i = j) (l : Fin n → TLay) (l' : Fin m → TLay) (i : Fin m) :
    extL e l l' (e i) = l' i := by
  have h : ∃ i', e i' = e i := ⟨i,rfl⟩
  unfold extL
  rw [dif_pos h,inj _ _ (Classical.choose_spec h)]

theorem extL_oth (l : Fin n → TLay) (l' : Fin m → TLay) {j : Fin n} (hj : ∀ i, e i ≠ j) :
    extL e l l' j = l j := by
  unfold extL
  rw [dif_neg (fun ⟨i,h⟩ => hj i h)]

end rs
section ext
variable {n m : Nat} {c T : Fin n → BitVec 64} {O : BitVec 64 → Prop} {D : BitVec 64 → Prop} {B : Bool}
  {ko : Fin n} {e : Fin m → Fin n} {ko' : Fin m}
  {H0 H' : BitVec 64} {M0 M : Mem} {Rr' Rx : BitVec 64 → Prop}

/-- Extension of a restricted registry at a later memory and heap pointer to the whole registry. -/
theorem regT_extend (inj : ∀ i j, e i = e j → i = j) {kA kB : Fin n} (hAB : kA ≠ kB)
    (h0 : RegT n c T O H0 M0 D B ko) (hko : ∀ i, e i ≠ ko)
    (sub : RegTR m (fun i => c (e i)) (fun i => T (e i)) O H' M D B ko' Rr') (le : H0.toNat ≤ H'.toNat)
    (hRr : ∀ x, Rr' x → RegRgM m (fun i => c (e i)) (fun i => T (e i)) M0 x ∨ Rx x ∨
      (H0.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (hRx : ∀ x, Rx x → O x ∧ ∀ i, x ≠ c i)
    (hoth : ∀ j, (∀ i, e i ≠ j) → ∀ x, OthFp c T M0 j x → M x = M0 x) :
    RegT n c T O H' M D B ko := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h0
  obtain ⟨l',pure',mem',_,_,rr'⟩ := sub
  have keepOth : ∀ j, (∀ i, e i ≠ j) → ∀ x, TFp (c j) (T j) (l j) x → M x = M0 x := fun j hj x hx => by
    refine hoth j hj x ?_
    rcases hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨_,_,_,_,_,_,_,_,_,(mem j).2,h⟩)
  have tabs := regPure_tabs pure mem le
  refine ⟨extL e l l',⟨fun j => ?_,fun j1 j2 ne => ?_,fun x hx j => ?_⟩,fun j => ?_,?_,?_⟩
  · by_cases hj : ∃ i, e i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [extL_sub inj]; exact pure'.1 i
    · have hj' : ∀ i, e i ≠ j := fun i h => hj ⟨i,h⟩
      rw [extL_oth _ _ hj']
      exact ⟨(tabs.1 j).2.1,(tabs.1 j).2.2.2⟩
  · by_cases h1 : ∃ i, e i = j1
    · obtain ⟨i1,rfl⟩ := h1
      rw [extL_sub inj]
      by_cases h2 : ∃ i, e i = j2
      · obtain ⟨i2,rfl⟩ := h2
        rw [extL_sub inj]
        exact pure'.2.1 i1 i2 (fun h => ne (congrArg e h))
      · have hj' : ∀ i, e i ≠ j2 := fun i h => h2 ⟨i,h⟩
        rw [extL_oth _ _ hj']
        exact sepSO hAB pure mem le (fun x hx => rr' i1 x (Or.inr (Or.inr hx))) hRr hRx hj'
    · have hj1 : ∀ i, e i ≠ j1 := fun i h => h1 ⟨i,h⟩
      rw [extL_oth _ _ hj1]
      by_cases h2 : ∃ i, e i = j2
      · obtain ⟨i2,rfl⟩ := h2
        rw [extL_sub inj]
        exact sepOS hAB pure mem le (fun x hx => rr' i2 x (Or.inr (Or.inr hx))) hRr hRx hj1
      · have hj' : ∀ i, e i ≠ j2 := fun i h => h2 ⟨i,h⟩
        rw [extL_oth _ _ hj']
        exact tabs.2.1 j1 j2 ne
  · by_cases hj : ∃ i, e i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [extL_sub inj]; exact pure'.2.2 x hx i
    · have hj' : ∀ i, e i ≠ j := fun i h => hj ⟨i,h⟩
      rw [extL_oth _ _ hj']
      exact tabs.2.2 x hx j
  · by_cases hj : ∃ i, e i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [extL_sub inj]; exact mem' i
    · have hj' : ∀ i, e i ≠ j := fun i h => hj ⟨i,h⟩
      rw [extL_oth _ _ hj']
      have fit := (pure.1 j).1.eEnd
      exact ⟨(keepOth j hj' _ (Or.inl rfl)).trans (mem j).1,
        hdr_keep (mem j).2 (by omega) (fun x lo hi => keepOth j hj' x (Or.inr (Or.inl ⟨lo,hi⟩)))⟩
  · rw [extL_oth _ _ hko]
    exact tc.frame (pure.1 ko).1.cnt.le (fun x hx => keepOth ko hko x (by
      rcases intabf_fp hx with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)))
  · rw [extL_oth _ _ hko]
    intro x hx
    have := ab x hx
    omega

#print axioms regT_extend
end ext
end InitECandidate.Runtime
