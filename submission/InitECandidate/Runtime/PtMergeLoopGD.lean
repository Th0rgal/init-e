import InitECandidate.Runtime.PtSrcOKGD
/-!
State of the `merge_tx_into_block` storage loop over the block map `bouter` (`bs + 32`): `MLW` says `bouter` is a ready
table whose values lie in the inner-table family `R` (`TabRV`, key length 20), the inner tables form an owned-region
family (`BTF`), the block map's physical region is below the heap pointer and apart from every inner region, every
current region is an entry region or fresh heap `[H0, H)`, and every word outside the entry regions below `H0` is as in
the entry memory `M0`. Pure steps: a union into an inner table, a set on `bouter` with a value in `R`, a fresh inner
table.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The storage-loop state with explicit witnesses: heap `H`, block-map bound `Hl`, layout `lb`, inner regions `Os`. -/
def MLW (D : BitVec 64 → Prop) (B : Bool) (BO : BitVec 64) (lb0 : TLay) (R0 : Set (BitVec 64))
    (Os0 : BitVec 64 → BitVec 64 → Prop) (H0 Nj : BitVec 64) (M0 : Mem) (R : Set (BitVec 64)) (H Hl : BitVec 64)
    (lb : TLay) (Os : BitVec 64 → BitVec 64 → Prop) (M : Mem) (G : GA) : Prop :=
  (HeapIs G H ∧ H0.toNat ≤ H.toNat ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) ∧
  (TabRV D B BO lb Hl R M ∧ Hl.toNat ≤ H.toNat ∧ lb.KL = 20#64 ∧ lb.SD.toNat ≤ 56) ∧
  BTF R Os H M ∧
  ((∀ x, TabPhys BO lb x → x.toNat < H.toNat) ∧ (∀ t ∈ R, ∀ x, Os t x → ¬ TabPhys BO lb x)) ∧
  ((∀ x, TabPhys BO lb x → TabPhys BO lb0 x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < H.toNat)) ∧
    (∀ t ∈ R, ∀ x, Os t x → (t ∈ R0 ∧ Os0 t x) ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < H.toNat)) ∧ R0 ⊆ R) ∧
  ∀ x, ¬ TabPhys BO lb0 x → (∀ t ∈ R0, ¬ Os0 t x) → x.toNat < H0.toNat → M x = M0 x

/-- The storage-loop state. -/
def MLR (D : BitVec 64 → Prop) (B : Bool) (BO : BitVec 64) (lb0 : TLay) (R0 : Set (BitVec 64))
    (Os0 : BitVec 64 → BitVec 64 → Prop) (H0 Nj : BitVec 64) (M0 : Mem) (R : Set (BitVec 64)) (M : Mem) (G : GA) :
    Prop :=
  ∃ (H Hl : BitVec 64) (lb : TLay) (Os : BitVec 64 → BitVec 64 → Prop), MLW D B BO lb0 R0 Os0 H0 Nj M0 R H Hl lb Os M G

section ml
variable {D : BitVec 64 → Prop} {B : Bool} {BO : BitVec 64} {lb0 : TLay} {R0 : Set (BitVec 64)}
  {Os0 : BitVec 64 → BitVec 64 → Prop} {H0 Nj : BitVec 64} {M0 : Mem} {R : Set (BitVec 64)} {H Hl : BitVec 64}
  {lb : TLay} {Os : BitVec 64 → BitVec 64 → Prop} {M M' : Mem} {G G' : GA}

/-- An entry-outside word below `H0` is outside every current region. -/
theorem mlw_out (m : MLW D B BO lb0 R0 Os0 H0 Nj M0 R H Hl lb Os M G) {x : BitVec 64} (h1 : ¬ TabPhys BO lb0 x)
    (h2 : ∀ t ∈ R0, ¬ Os0 t x) (h3 : x.toNat < H0.toNat) :
    ¬ TabPhys BO lb x ∧ (∀ t ∈ R, ¬ Os t x) ∧ x.toNat < H.toNat := by
  obtain ⟨⟨_,h0,_⟩,_,_,_,⟨bgr,ogr,_⟩,_⟩ := m
  refine ⟨fun h => ?_,fun t ht h => ?_,by omega⟩
  · rcases bgr x h with h | ⟨h,_⟩
    · exact h1 h
    · omega
  · rcases ogr t ht x h with ⟨t0,h⟩ | ⟨h,_⟩
    · exact h2 t t0 h
    · omega

/-- A union into the inner table `b ∈ R`. -/
theorem mlw_union {b : BitVec 64} (hb : b ∈ R) (m : MLW D B BO lb0 R0 Os0 H0 Nj M0 R H Hl lb Os M G)
    (u : UOS (Os b) b H Nj M M' G') : MLR D B BO lb0 R0 Os0 H0 Nj M0 R M' G' := by
  obtain ⟨⟨hH,h0,hn⟩,⟨rv,hHl,kl,sd⟩,f,⟨bph,bdis⟩,⟨bgr,ogr,r0⟩,fr⟩ := m
  obtain ⟨H',hH',le,f',hn',fr'⟩ := btf_union hb f u
  refine ⟨H',Hl,lb,_,⟨hH',by omega,hn'⟩,⟨tabRV_frame rv (fun x hx => fr' x (fun h => bdis b hb x h hx) (bph x hx)),
    by omega,kl,sd⟩,f',⟨fun x hx => by have := bph x hx; omega,fun t ht x hx hp => ?_⟩,
    ⟨fun x hx => ?_,fun t ht x hx => ?_,r0⟩,fun x h1 h2 h3 => ?_⟩
  · rcases hx with h | ⟨_,h,_⟩
    · exact bdis t ht x h hp
    · have := bph x hp; omega
  · rcases bgr x hx with h | ⟨h1,h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1,by omega⟩
  · rcases hx with h | ⟨_,h1,h2⟩
    · rcases ogr t ht x h with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1,by omega⟩
    · exact Or.inr ⟨by omega,h2⟩
  · refine (fr' x (fun h => ?_) (by omega)).trans (fr x h1 h2 h3)
    rcases ogr b hb x h with ⟨t0,h⟩ | ⟨h,_⟩
    · exact h2 b t0 h
    · omega

#print axioms mlw_union

/-- A set on `bouter` (values in `R`): kept outside its physical region below `H`, exit layout located. -/
theorem mlw_set (m : MLW D B BO lb0 R0 Os0 H0 Nj M0 R H Hl lb Os M G)
    (fr : ∀ x, ¬ TabPhys BO lb x → x.toNat < H.toNat → M' x = M x)
    (hn' : G'.lookup (ofString "journal_n") = some (.val (.word Nj))) (srv : SetRV D B BO lb H R M' G') :
    MLR D B BO lb0 R0 Os0 H0 Nj M0 R M' G' := by
  obtain ⟨⟨hH,h0,hn⟩,⟨rv,hHl,kl,sd⟩,⟨ft,fb,fd⟩,⟨bph,bdis⟩,⟨bgr,ogr,r0⟩,fr0⟩ := m
  obtain ⟨l',Hp,hHp,le,rv',ekl,esd,ph⟩ := srv
  have keepO : ∀ t ∈ R, ∀ x, Os t x → M' x = M x := fun t ht x hx => fr x (bdis t ht x hx) (fb t ht x hx)
  refine ⟨Hp,Hp,l',Os,⟨hHp,by omega,hn'⟩,⟨rv',le_refl _,by rw [ekl]; exact kl,by rw [esd]; exact sd⟩,
    ⟨fun t ht => tabO_mono (tabO_frame (ft t ht) (keepO t ht)) le,fun t ht x hx => by have := fb t ht x hx; omega,fd⟩,
    ⟨fun x hx => ?_,fun t ht x hx hp => ?_⟩,⟨fun x hx => ?_,fun t ht x hx => ?_,r0⟩,fun x h1 h2 h3 => ?_⟩
  · rcases ph x hx with h | ⟨_,h⟩
    · have := bph x h; omega
    · exact h
  · rcases ph x hp with h | ⟨h,_⟩
    · exact bdis t ht x hx h
    · have := fb t ht x hx; omega
  · rcases ph x hx with h | ⟨h1,h2⟩
    · rcases bgr x h with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1,by omega⟩
    · exact Or.inr ⟨by omega,h2⟩
  · rcases ogr t ht x hx with h | ⟨h1,h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1,by omega⟩
  · obtain ⟨o1,_,o3⟩ := mlw_out (⟨⟨hH,h0,hn⟩,⟨rv,hHl,kl,sd⟩,⟨ft,fb,fd⟩,⟨bph,bdis⟩,⟨bgr,ogr,r0⟩,fr0⟩ :
      MLW D B BO lb0 R0 Os0 H0 Nj M0 R H Hl lb Os M G) h1 h2 h3
    exact (fr x o1 o3).trans (fr0 x h1 h2 h3)

#print axioms mlw_set

/-- A fresh inner table `Tt` (valid in `[Tt, H')`, `Tt ≥ H`, memory below `H` kept) joins the family. -/
theorem mlw_new {Tt H' : BitVec 64} (m : MLW D B BO lb0 R0 Os0 H0 Nj M0 R H Hl lb Os M G)
    (hHT : H.toNat ≤ Tt.toNat) (hH' : HeapIs G' H') (hT : Tt.toNat + 72 ≤ H'.toNat)
    (hn' : G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (fr : ∀ x, x.toNat < H.toNat → M' x = M x) (tv : TabV Tt Tt H' M') :
    Tt ∉ R ∧ MLW D B BO lb0 R0 Os0 H0 Nj M0 (insert Tt R) H' Hl lb
      (fun t x => (t ≠ Tt ∧ Os t x) ∨ (t = Tt ∧ H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) M' G' := by
  obtain ⟨⟨hH,h0,hn⟩,⟨rv,hHl,kl,sd⟩,⟨ft,fb,fd⟩,⟨bph,bdis⟩,⟨bgr,ogr,r0⟩,fr0⟩ := m
  have nR : Tt ∉ R := fun h => by
    obtain ⟨l,lay,_,ho,_⟩ := ft Tt h
    have := fb Tt h Tt (ho Tt (le_refl _) (by have := lay.eEnd; omega)); omega
  have newO : TabO (fun x => H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat) Tt H' M' := by
    obtain ⟨KL,SD,C,N,KS,VS,US,OS,OPS,b,lay,hd,a,li⟩ := tv
    exact ⟨⟨KL,SD,C,N,KS,VS,US,OS,OPS,b⟩,lay,hd,fun x lo hi => ⟨by omega,by omega⟩,
      fun x hx => let ⟨h1,h2⟩ := li x hx; ⟨by omega,h2⟩⟩
  have inR : ∀ t, t ∈ insert Tt R → t ≠ Tt → t ∈ R := fun t ht ne => ht.resolve_left ne
  refine ⟨nR,⟨hH',by omega,hn'⟩,⟨tabRV_mono (tabRV_frame rv (fun x hx => fr x (bph x hx))) (le_refl _) (fun t h => Or.inr h),
    by omega,kl,sd⟩,
    ⟨fun t ht => ?_,fun t ht x hx => ?_,fun t ht t' ht' ne x hx hx' => ?_⟩,
    ⟨fun x hx => by have := bph x hx; omega,fun t ht x hx hp => ?_⟩,⟨fun x hx => ?_,fun t ht x hx => ?_,
      fun t h => Or.inr (r0 h)⟩,fun x h1 h2 h3 => (fr x (by omega)).trans (fr0 x h1 h2 h3)⟩
  · by_cases e : t = Tt
    · subst e
      exact tabO_sub newO (fun x h => Or.inr ⟨rfl,h⟩)
    · have tR := inR t ht e
      exact tabO_sub (tabO_mono (tabO_frame (ft t tR) (fun x hx => fr x (fb t tR x hx))) (by omega))
        (fun x h => Or.inl ⟨e,h⟩)
  · rcases hx with ⟨e,h⟩ | ⟨_,_,h⟩
    · have := fb t (inR t ht e) x h; omega
    · exact h
  · rcases hx with ⟨e,h⟩ | ⟨e,h1,_⟩ <;> rcases hx' with ⟨e',h'⟩ | ⟨e',h1',_⟩
    · exact fd t (inR t ht e) t' (inR t' ht' e') ne x h h'
    · have := fb t (inR t ht e) x h; omega
    · have := fb t' (inR t' ht' e') x h'; omega
    · exact ne (e.trans e'.symm)
  · rcases hx with ⟨e,h⟩ | ⟨_,h,_⟩
    · exact bdis t (inR t ht e) x h hp
    · have := bph x hp; omega
  · rcases bgr x hx with h | ⟨h1,h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1,by omega⟩
  · rcases hx with ⟨e,h⟩ | ⟨_,h1,h2⟩
    · rcases ogr t (inR t ht e) x h with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1,by omega⟩
    · exact Or.inr ⟨by omega,h2⟩

#print axioms mlw_new
end ml
end InitECandidate.Runtime
