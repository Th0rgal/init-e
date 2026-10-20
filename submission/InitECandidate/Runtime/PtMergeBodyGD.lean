import InitECandidate.Runtime.PtMergeTailGD
/-!
The actual `merge_tx_into_block` body: the five head unions into members of the block-table family `R` (`MHS`), then
the storage loop (`MLR`) whose inner family is the same `R`. From the storage-loop state at merge entry (heap `He`,
memory `Me`), a return gives `0` and the storage-loop state relative to the merge entry.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section mb
variable {D : BitVec 64 → Prop} {B : Bool} {BO : BitVec 64} {lb0 : TLay} {R : Set (BitVec 64)}
  {Ose : BitVec 64 → BitVec 64 → Prop} {He Hl Nj : BitVec 64} {Me : Mem} {Ge : GA}

/-- The head exit as a storage-loop entry. -/
theorem mlw_of_mhs (we : MLW D B BO lb0 R Ose He Nj Me R He Hl lb0 Ose Me Ge) {M : Mem} {G : GA} {H : BitVec 64}
    {Os : BitVec 64 → BitVec 64 → Prop} (hH : HeapIs G H) (le : He.toNat ≤ H.toNat) (f : BTF R Os H M)
    (gr : ∀ t x, Os t x → Ose t x ∨ (He.toNat ≤ x.toNat ∧ x.toNat < H.toNat))
    (hn : G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (fr : ∀ x, (∀ t ∈ R, ¬ Ose t x) → x.toNat < He.toNat → M x = Me x) :
    MLW D B BO lb0 R Os H Nj M R H Hl lb0 Os M G := by
  obtain ⟨_,⟨rv,hHl,kl,sd⟩,_,⟨bph,bdis⟩,_,_⟩ := we
  refine ⟨⟨hH,le_refl _,hn⟩,⟨tabRV_frame rv (fun x hx => fr x (fun t ht h => bdis t ht x h hx) (bph x hx)),by omega,
    kl,sd⟩,f,⟨fun x hx => by have := bph x hx; omega,fun t ht x hx hp => ?_⟩,
    ⟨fun x hx => Or.inl hx,fun t ht x hx => Or.inl ⟨ht,hx⟩,fun _ h => h⟩,fun _ _ _ _ => rfl⟩
  rcases gr t x hx with h | ⟨h,_⟩
  · exact bdis t ht x h hp
  · have := bph x hp; omega

/-- A storage-loop state relative to the head exit is one relative to the merge entry. -/
theorem mlr_compose {M' : Mem} {H : BitVec 64}
    {Os : BitVec 64 → BitVec 64 → Prop} {R' : Set (BitVec 64)} {M : Mem} {G : GA} (le : He.toNat ≤ H.toNat)
    (gr : ∀ t x, Os t x → Ose t x ∨ (He.toNat ≤ x.toNat ∧ x.toNat < H.toNat))
    (frH : ∀ x, (∀ t ∈ R, ¬ Ose t x) → x.toNat < He.toNat → M' x = Me x)
    (mr : MLR D B BO lb0 R Os H Nj M' R' M G) : MLR D B BO lb0 R Ose He Nj Me R' M G := by
  obtain ⟨H2,Hl2,lb,Os2,⟨hH2,le2,hn2⟩,rvp,f2,bb,⟨bgr,ogr,r0⟩,fr2⟩ := mr
  refine ⟨H2,Hl2,lb,Os2,⟨hH2,by omega,hn2⟩,rvp,f2,bb,⟨fun x hx => ?_,fun t ht x hx => ?_,r0⟩,fun x h1 h2 h3 => ?_⟩
  · rcases bgr x hx with h | ⟨h1,h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega,h2⟩
  · rcases ogr t ht x hx with ⟨tR,h⟩ | ⟨h1,h2⟩
    · rcases gr t x h with h | ⟨h1,h2⟩
      · exact Or.inl ⟨tR,h⟩
      · exact Or.inr ⟨h1,by omega⟩
    · exact Or.inr ⟨by omega,h2⟩
  · refine (fr2 x h1 (fun t ht h => ?_) (by omega)).trans (frH x h2 h3)
    rcases gr t x h with h | ⟨h,_⟩
    · exact h2 t ht h
    · omega
end mb

section bd
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `merge_tx_into_block` body from the storage-loop state at entry (`Me`, `Ge`). -/
theorem mergeBody_aqgd (BO : BitVec 64) (lb0 : TLay) (R : Set (BitVec 64)) (Ose : BitVec 64 → BitVec 64 → Prop)
    (He Hl Nj : BitVec 64) (Me : Mem) (Ge : GA) (we : MLW D B BO lb0 R Ose He Nj Me R He Hl lb0 Ose Me Ge)
    (O : BitVec 64) (lo : TLay) (tc0 : TCont D B Me O lo) (kl0 : 20 ≤ lo.KL.toNat) (nc0 : lo.N.toNat < lo.C.toNat)
    (hOp : ∀ x, InTabF O lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x →
      ¬ TabPhys BO lb0 x ∧ (∀ t ∈ R, ¬ Ose t x) ∧ x.toNat < He.toNat)
    (Ts Bs : BitVec 64) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcell : ∀ k : BitVec 64, k = 8#64 ∨ k = 16#64 ∨ k = 24#64 ∨ k = 32#64 ∨ k = 40#64 ∨ k = 48#64 →
      (D (Bs + k) ∧ (∀ t ∈ R, ¬ Ose t (Bs + k)) ∧ (Bs + k).toNat < He.toNat) ∧
      (D (Ts + k) ∧ (∀ t ∈ R, ¬ Ose t (Ts + k)) ∧ (Ts + k).toNat < He.toNat))
    (j24 j8 j40 j16 j48 : BitVec 64) (hj24 : j24 ∈ R) (hj8 : j8 ∈ R) (hj40 : j40 ∈ R) (hj16 : j16 ∈ R)
    (hj48 : j48 ∈ R) (cb24 : Me (Bs + 24#64) = .word j24) (cb8 : Me (Bs + 8#64) = .word j8)
    (cb40 : Me (Bs + 40#64) = .word j40) (cb16 : Me (Bs + 16#64) = .word j16) (cb48 : Me (Bs + 48#64) = .word j48)
    (cT : Me (Ts + 32#64) = .word O) (cB : Me (Bs + 32#64) = .word BO)
    (hwB : ¬ TabPhys BO lb0 w) (hwO : ∀ t ∈ R, ¬ Ose t w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ He.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun _ M G => M = Me ∧ G = Ge)
      (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ ∃ R' : Set (BitVec 64), MLR D B BO lb0 R Ose He Nj Me R' M G)
      (sourceFunctionBody Guest.guestFn_merge_tx_into_block) := by
  have ex : ∀ a : BitVec 64, ∃ y : BitVec 64, Me a = .word y := fun a => by
    cases h : Me a with | word y => exact ⟨y,rfl⟩
  obtain ⟨y24,ct24⟩ := ex (Ts + 24#64)
  obtain ⟨y8,ct8⟩ := ex (Ts + 8#64)
  obtain ⟨y40,ct40⟩ := ex (Ts + 40#64)
  obtain ⟨y16,ct16⟩ := ex (Ts + 16#64)
  obtain ⟨y48,ct48⟩ := ex (Ts + 48#64)
  obtain ⟨⟨b24,t24⟩⟩ := (⟨hcell 24#64 (by simp)⟩ : Nonempty _)
  obtain ⟨⟨b8,t8⟩⟩ := (⟨hcell 8#64 (by simp)⟩ : Nonempty _)
  obtain ⟨⟨b40,t40⟩⟩ := (⟨hcell 40#64 (by simp)⟩ : Nonempty _)
  obtain ⟨⟨b16,t16⟩⟩ := (⟨hcell 16#64 (by simp)⟩ : Nonempty _)
  obtain ⟨⟨b48,t48⟩⟩ := (⟨hcell 48#64 (by simp)⟩ : Nonempty _)
  obtain ⟨⟨b32,t32⟩⟩ := (⟨hcell 32#64 (by simp)⟩ : Nonempty _)
  have we' := we
  obtain ⟨⟨hHe,_,hne⟩,_,fe,_,_,_⟩ := we'
  rw [source_merge_body_explicit]
  simp only [unionChain,mergeUnionCall]
  refine aqgd_conseq (P := fun L M G => (fun _ => True) L ∧ MHS R Ose He Nj Me M G) ?_
    (fun L M G ⟨hM,hG⟩ => ⟨trivial,by rw [hM,hG]; exact mhs_init fe hHe hne⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine mergeHeadF_aqgd (LP := fun _ => True) R Ose Bs Ts He Nj Me hBs hTs j24 y24 hj24 b24.1 cb24 b24.2.1 b24.2.2
    t24.1 ct24 t24.2.1 t24.2.2 j8 y8 hj8 b8.1 cb8 b8.2.1 b8.2.2 t8.1 ct8 t8.2.1 t8.2.2
    j40 y40 hj40 b40.1 cb40 b40.2.1 b40.2.2 t40.1 ct40 t40.2.1 t40.2.2
    j16 y16 hj16 b16.1 cb16 b16.2.1 b16.2.2 t16.1 ct16 t16.2.1 t16.2.2
    j48 y48 hj48 b48.1 cb48 b48.2.1 b48.2.2 t48.1 ct48 t48.2.1 t48.2.2 hwO hwP p0 ?_
  refine aqgd_conseq (P := fun L M G => ∃ q : (BitVec 64 × (BitVec 64 → BitVec 64 → Prop)) × Mem,
      (M = q.2 ∧ MLR D B BO lb0 R q.1.2 q.1.1 Nj q.2 R M G) ∧ (He.toNat ≤ q.1.1.toNat ∧
        (∀ t x, q.1.2 t x → Ose t x ∨ (He.toNat ≤ x.toNat ∧ x.toNat < q.1.1.toNat)) ∧
        (∀ x, (∀ t ∈ R, ¬ Ose t x) → x.toNat < He.toNat → q.2 x = Me x)))
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨_,H,Os,hH,le,f,gr,hn,fr⟩ =>
      ⟨((H,Os),M),⟨rfl,H,Hl,lb0,Os,mlw_of_mhs we hH le f gr hn fr⟩,le,gr,fr⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨⟨H,Os⟩,Mh⟩
  refine aqgd_pureE (fun ⟨le,gr,frH⟩ => ?_)
  dsimp only at le gr frH
  have hOpH : ∀ x, InTabF O lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x →
      ¬ TabPhys BO lb0 x ∧ (∀ t ∈ R, ¬ Os t x) ∧ x.toNat < H.toNat := fun x hx => by
    obtain ⟨a,b,c⟩ := hOp x hx
    refine ⟨a,fun t ht h => ?_,by omega⟩
    rcases gr t x h with h | ⟨h,_⟩
    · exact b t ht h
    · omega
  have tcH : TCont D B Mh O lo := tc0.frame (Nat.le_of_lt nc0) (fun x hx => frH x (hOp x hx).2.1 (hOp x hx).2.2)
  have hwOH : ∀ t ∈ R, ¬ Os t w := fun t ht h => by
    rcases gr t w h with h | ⟨h,_⟩
    · exact hwO t ht h
    · omega
  refine aqgd_conseq (mergeTail_aqgd BO lb0 R Os H Nj Mh O lo tcH kl0 nc0 hOpH hwB hwOH hwP (by omega) Dall Ts Bs hTs
      hBs t32.1 (by rw [frH _ t32.2.1 t32.2.2]; exact cT) b32.1 (by rw [frH _ b32.2.1 b32.2.2]; exact cB))
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun v M G ⟨hv,R',mr⟩ => ⟨hv,R',mlr_compose le gr frH mr⟩)

#print axioms mergeBody_aqgd
end bd
end InitECandidate.Runtime
