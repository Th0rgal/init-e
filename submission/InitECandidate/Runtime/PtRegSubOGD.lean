import InitECandidate.Runtime.PtRegSubGD
/-!
Sub-registries keeping the content table, with the other tables as outside objects. Restricting along an injective
index map `e` whose image contains the content table `ko` makes the cells, headers and arrays of the tables outside the
image outside words of the restriction (`regT_restrict_out`); a restriction at a later memory and heap pointer extends
back to the whole registry when those footprints were kept (`regT_extend_out`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ro
variable {n m : Nat} {c T : Fin n → BitVec 64} {O : BitVec 64 → Prop} {D : BitVec 64 → Prop} {B : Bool}
  {ko : Fin n} {e : Fin m → Fin n} {ko' : Fin m}

/-- Outside words of a restriction: the registry's outside words and the footprints (read off `M0`) of the tables
outside the image. -/
def OutSub (O : BitVec 64 → Prop) (c T : Fin n → BitVec 64) (e : Fin m → Fin n) (M0 : Mem) (x : BitVec 64) : Prop :=
  O x ∨ ∃ j, (∀ i, e i ≠ j) ∧ OthFp c T M0 j x

theorem othFp_of_tfp {M0 : Mem} {l : Fin n → TLay} (mem : RegMem n c T l M0) {j : Fin n} {x : BitVec 64}
    (h : TFp (c j) (T j) (l j) x) : OthFp c T M0 j x := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨_,_,_,_,_,_,_,_,_,(mem j).2,h⟩)

theorem tfp_of_othFp {M0 : Mem} {l : Fin n → TLay} (mem : RegMem n c T l M0) {j : Fin n} {x : BitVec 64}
    (h : OthFp c T M0 j x) : TFp (c j) (T j) (l j) x := by
  rcases h with h | h | ⟨KL,SD,C,N,KS,VS,US,OS,OPS,hd,ha⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨_,e1,e2,_,e4,e5,e6,e7,e8⟩ := hdr_unique hd (mem j).2
    refine Or.inr (Or.inr ?_)
    show ArrOf (l j).C (l j).SD (l j).KS (l j).VS (l j).US (l j).OS (l j).OPS x
    rw [e1,e2,e4,e5,e6,e7,e8]; exact ha

/-- Restriction keeping the content table; the other tables become outside objects. -/
theorem regT_restrict_out {H : BitVec 64} {M : Mem} (inj : ∀ i j, e i = e j → i = j) (hko : e ko' = ko)
    (h : RegT n c T O H M D B ko) :
    RegT m (fun i => c (e i)) (fun i => T (e i)) (OutSub O c T e M) H M D B ko' := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  refine ⟨fun i => l (e i),⟨fun i => pure.1 (e i),fun i j ne => pure.2.1 _ _ (fun h => ne (inj _ _ h)),
    fun x hx i => ?_⟩,fun i => mem (e i),?_,?_⟩
  · rcases hx with ho | ⟨j,hj,hfp⟩
    · exact pure.2.2 x ho (e i)
    · exact pure.2.1 (e i) j (hj i) x (tfp_of_othFp mem hfp)
  · show TCont D B M (T (e ko')) (l (e ko')); rw [hko]; exact tc
  · intro x hx
    show x.toNat < H.toNat
    have : (l (e ko')).arr x := hx
    rw [hko] at this; exact ab x this

#print axioms regT_restrict_out

/-- Extension of a restriction keeping the content table, at a later memory and heap pointer, when the footprints
of the other tables were kept. -/
theorem regT_extend_out {H0 H' : BitVec 64} {M0 M : Mem} (inj : ∀ i j, e i = e j → i = j) (hko : e ko' = ko)
    {kA kB : Fin m} (hAB : kA ≠ kB)
    (h0 : RegT n c T O H0 M0 D B ko)
    (sub : RegT m (fun i => c (e i)) (fun i => T (e i)) (OutSub O c T e M0) H' M D B ko')
    (le : H0.toNat ≤ H'.toNat)
    (hoth : ∀ j, (∀ i, e i ≠ j) → ∀ x, OthFp c T M0 j x → M x = M0 x) :
    RegT n c T O H' M D B ko := by
  obtain ⟨l,pure,mem,_,_⟩ := h0
  obtain ⟨l',pure',mem',tc',ab'⟩ := sub
  have tabs := regPure_tabs pure mem le
  have keepOth : ∀ j, (∀ i, e i ≠ j) → ∀ x, TFp (c j) (T j) (l j) x → M x = M0 x := fun j hj x hx =>
    hoth j hj x (othFp_of_tfp mem hx)
  have outOth : ∀ j, (∀ i, e i ≠ j) → ∀ x, TFp (c j) (T j) (l j) x → OutSub O c T e M0 x := fun j hj x hx =>
    Or.inr ⟨j,hj,othFp_of_tfp mem hx⟩
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
        exact fun x hx hc => pure'.2.2 x (outOth j2 hj' x hx) i1 hc
    · have hj1 : ∀ i, e i ≠ j1 := fun i h => h1 ⟨i,h⟩
      rw [extL_oth _ _ hj1]
      by_cases h2 : ∃ i, e i = j2
      · obtain ⟨i2,rfl⟩ := h2
        rw [extL_sub inj]
        intro x hx hc
        have hc' := canon_mono hc le
        have ne' : j1 ≠ e i2 := fun h => hj1 i2 h.symm
        rcases hx with hce | hh | ha
        · exact pure.2.1 j1 (e i2) ne' x (Or.inl hce) hc'
        · exact pure.2.1 j1 (e i2) ne' x (Or.inr (Or.inl hh)) hc'
        · have hlt := regPure_arr_below pure' hAB i2 ha
          rcases hc with hh | ha2 | hge
          · exact pure'.2.2 x (outOth j1 hj1 x (Or.inr (Or.inl hh))) i2 (Or.inr (Or.inl ha))
          · exact pure'.2.2 x (outOth j1 hj1 x (Or.inr (Or.inr ha2))) i2 (Or.inr (Or.inl ha))
          · omega
      · have hj' : ∀ i, e i ≠ j2 := fun i h => h2 ⟨i,h⟩
        rw [extL_oth _ _ hj']
        exact tabs.2.1 j1 j2 ne
  · by_cases hj : ∃ i, e i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [extL_sub inj]; exact pure'.2.2 x (Or.inl hx) i
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
  · rw [← hko,extL_sub inj]; exact tc'
  · rw [← hko,extL_sub inj]; exact ab'

#print axioms regT_extend_out
end ro
end InitECandidate.Runtime
