import InitECandidate.Runtime.PtBalCallGD
/-!
The actual `bal_ensure_account(addr)`: from the block-access-list state (`BalW`), a return gives a live account record
and the state relative to the entry (`BalStep`: live accounts and regions only grown by fresh heap, every word below the
entry heap pointer outside the entry regions kept).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The block-access-list state after a step from (`ADs`, `Rg`, `H`, `M1`). -/
def BalStep (D : BitVec 64 → Prop) (B : Bool) (BA IA IS KB : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ (ADs' : Set (BitVec 64)) (Rg' : BalK → BitVec 64 → Prop) (H' : BitVec 64), HeapIs G H' ∧ H.toNat ≤ H'.toNat ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalW D B BA IA IS KB ADs' Rg' H' M ∧ ADs ⊆ ADs' ∧
    (∀ c, BalK.live ADs' c → ∀ x, Rg' c x → (BalK.live ADs c ∧ Rg c x) ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
    ∀ x, x.toNat < H.toNat → (∀ c, BalK.live ADs c → ¬ Rg c x) → M x = M1 x

/-- `BalStep` with the account `ad` live after the step. -/
def BalStepA (D : BitVec 64 → Prop) (B : Bool) (BA IA IS KB : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (ad : BitVec 64) (M : Mem) (G : GA) : Prop :=
  ∃ (ADs' : Set (BitVec 64)) (Rg' : BalK → BitVec 64 → Prop) (H' : BitVec 64), HeapIs G H' ∧ H.toNat ≤ H'.toNat ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalW D B BA IA IS KB ADs' Rg' H' M ∧ ADs ⊆ ADs' ∧
    (∀ c, BalK.live ADs' c → ∀ x, Rg' c x → (BalK.live ADs c ∧ Rg c x) ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
    (∀ x, x.toNat < H.toNat → (∀ c, BalK.live ADs c → ¬ Rg c x) → M x = M1 x) ∧ ad ∈ ADs'

section bs
variable {D : BitVec 64 → Prop} {B : Bool} {BA IA IS KB : BitVec 64} {ADs : Set (BitVec 64)}
  {Rg : BalK → BitVec 64 → Prop} {H Nj : BitVec 64} {M1 : Mem} {G1 : GA}

theorem balStep_refl (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH : HeapIs G1 H)
    (hn : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) :
    BalStep D B BA IA IS KB ADs Rg H Nj M1 M1 G1 :=
  ⟨ADs,Rg,H,hH,le_refl _,hn,bw,fun _ h => h,fun c hc x hx => Or.inl ⟨hc,hx⟩,fun _ _ _ => rfl⟩
end bs

/-- A component of the record under construction: a word stored at `ad + off` (once stored) naming an object valid in
the fresh interval `[lo, hi)`. -/
def CompV (D : BitVec 64 → Prop) (B : Bool) (k : Nat) (obj : BitVec 64) (lo hi : BitVec 64) (H : BitVec 64)
    (M : Mem) : Prop :=
  match k with
  | 0 => ∃ Hl : BitVec 64, TabRV D B obj (newLay obj 32#64 8#64 3) Hl ∅ M ∧ Hl.toNat ≤ H.toNat ∧
      ∀ x, TabPhys obj (newLay obj 32#64 8#64 3) x → lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat
  | 1 => TabO (fun x => lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat) obj H M
  | 2 => LstO 40#64 (fun x => lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat) obj M
  | 3 => LstO 16#64 (fun x => lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat) obj M
  | _ => LstO 24#64 (fun x => lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat) obj M

section cv
variable {D : BitVec 64 → Prop} {B : Bool}

theorem compV_frame {k : Nat} {obj lo hi H : BitVec 64} {M M' : Mem} (h : CompV D B k obj lo hi H M)
    (keep : ∀ x : BitVec 64, lo.toNat ≤ x.toNat → x.toNat < hi.toNat → M' x = M x) : CompV D B k obj lo hi H M' := by
  match k, h with
  | 0, ⟨Hl,rv,a,b⟩ => exact ⟨Hl,tabRV_frame rv (fun x hx => keep x (b x hx).1 (b x hx).2),a,b⟩
  | 1, h => exact tabO_frame h (fun x hx => keep x hx.1 hx.2)
  | 2, h => exact lstO_frame h (fun x hx => keep x hx.1 hx.2)
  | 3, h => exact lstO_frame h (fun x hx => keep x hx.1 hx.2)
  | k + 4, h => exact lstO_frame h (fun x hx => keep x hx.1 hx.2)

theorem compV_mono {k : Nat} {obj lo hi H H' : BitVec 64} {M : Mem} (h : CompV D B k obj lo hi H M)
    (le : H.toNat ≤ H'.toNat) : CompV D B k obj lo hi H' M := by
  match k, h with
  | 0, ⟨Hl,rv,a,b⟩ => exact ⟨Hl,rv,by omega,b⟩
  | 1, h => exact tabO_mono h le
  | 2, h => exact h
  | 3, h => exact h
  | k + 4, h => exact h
end cv

/-- A fresh table that is both `NewTab` (exit heap `H'`) and `TabRV` with the fresh layout lies in `[T, H')` and its
readiness bound is at most `H'`. -/
theorem newRV_loc {D : BitVec 64 → Prop} {B : Bool} {T H' KL Cp Hl : BitVec 64} {b : Nat} {M : Mem}
    (nt : NewTab T H' KL Cp M) (rv : TabRV D B T (newLay T KL Cp b) Hl ∅ M)
    (hHl : Hl = allocationEnd (htabNewOrderPos T KL Cp) (Cp * 8)) :
    Hl.toNat ≤ H'.toNat ∧ ∀ x, TabPhys T (newLay T KL Cp b) x → T.toNat ≤ x.toNat ∧ x.toNat < H'.toNat := by
  obtain ⟨_,s,_,hm,_,_,_,_,_,_,rd,_⟩ := rv
  obtain ⟨KS,VS,US,OS,OPS,hd,_,_,_,_,_,_,_,_,_,_,_,p2⟩ := nt
  have a := rd.live.arrays
  have c64 : s.memory (T + 64#64) = .word (newLay T KL Cp b).OPS := a.cell64
  rw [hm,hd.2.2.2.2.2.2.2.2] at c64
  simp only [HolWordLab.word.injEq] at c64
  have hk := a.headerKeys; have hv := a.headerValues; have kb := a.keysBefore; have vb := a.valuesBefore
  have ub := a.usedBefore; have ob := a.orderBefore; have eb := a.endBound; have oa := a.orderPosAligned
  simp only [newLay] at hk hv kb vb ub ob eb oa ⊢
  have c8 : (Cp * 8#64).toNat = Cp.toNat * 8 := by rw [BitVec.toNat_mul]; simp; omega
  rw [c64,c8] at p2
  simp only [newLay] at p2
  have e : Hl.toNat = (htabNewOrderPos T KL Cp).toNat + Cp.toNat * 8 := by
    rw [hHl,allocationEnd_toNat _ _ (by rw [show (Cp * 8 : BitVec 64) = Cp * 8#64 from rfl,c8]; omega),
      show (Cp * 8 : BitVec 64) = Cp * 8#64 from rfl,c8]
    omega
  refine ⟨by omega,fun x hx => ?_⟩
  unfold TabPhys InTabF at hx
  simp only [newLay] at hx
  have : (allocationEnd T 72).toNat ≤ (allocationEnd T 72).toNat + Cp.toNat * (allocationEnd 0 KL).toNat :=
    Nat.le_add_right _ _
  rcases hx with h | h | h | h | h | h <;> constructor <;> omega

#print axioms newRV_loc

section st
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A word store whose address and value evaluate (from the precondition) to words `a`, `y`, `a ≠ w`. -/
theorem aqgd_storeW {P Q : GA → Mem → GA → Prop} (d v : ExpHOL 64)
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → DomD D B s → P s.locals s.memory s.globals →
      ∃ a y : BitVec 64, EV s d = some (.val (.word a)) ∧ EV s v = some (.val (.word y)) ∧ w ≠ a ∧
        Q s.locals (fun x => if x = a then .word y else s.memory x) s.globals) :
    AQGD D B A w Vn P Q RR (.store d v) := by
  refine aqgd_storeD d v (fun s H aw dom hG pre _ => ?_) (fun s x H aw dom hG pre _ ev => ?_)
  · unfold GIs at hG; subst hG
    obtain ⟨a,y,ea,ev,ne,q⟩ := h s aw dom pre
    exact ⟨a,ea,ne,fun y' ev' => by rw [ev] at ev'; simp only [Option.some.injEq,ValueHOL.val.injEq,
      HolWordLab.word.injEq] at ev'; subst ev'; exact q⟩
  · unfold GIs at hG; subst hG
    obtain ⟨a,y,_,ev2,_,_⟩ := h s aw dom pre
    rw [ev2] at ev
    exact ⟨y,(Option.some.inj ev).symm⟩

#print axioms aqgd_storeW
end st

/-- Regions of a freshly built account record: record words, then the five components in consecutive intervals. -/
def adRgs (H H1 H2 H3 H4 H5 H6 : BitVec 64) : AdC → BitVec 64 → Prop
  | .recw, x => H.toNat ≤ x.toNat ∧ x.toNat < H.toNat + 40
  | .t0, x => H1.toNat ≤ x.toNat ∧ x.toNat < H2.toNat
  | .t8, x => H2.toNat ≤ x.toNat ∧ x.toNat < H3.toNat
  | .l16, x => H3.toNat ≤ x.toNat ∧ x.toNat < H4.toNat
  | .l24, x => H4.toNat ≤ x.toNat ∧ x.toNat < H5.toNat
  | .l32, x => H5.toNat ≤ x.toNat ∧ x.toNat < H6.toNat
  | .lst _, _ => False

theorem adRgs_dis {H H1 H2 H3 H4 H5 H6 : BitVec 64} (o1 : H.toNat + 40 ≤ H1.toNat) (o2 : H1.toNat ≤ H2.toNat)
    (o3 : H2.toNat ≤ H3.toNat) (o4 : H3.toNat ≤ H4.toNat) (o5 : H4.toNat ≤ H5.toNat) :
    RgDis (AdC.live ∅) (adRgs H H1 H2 H3 H4 H5 H6) := by
  intro c c' hc hc' ne x h1 h2
  cases c <;> cases c' <;> first
    | exact ne rfl
    | (simp only [adRgs] at h1 h2 <;> omega)

theorem adRgs_in {H H1 H2 H3 H4 H5 H6 : BitVec 64} (o1 : H.toNat + 40 ≤ H1.toNat) (o2 : H1.toNat ≤ H2.toNat)
    (o3 : H2.toNat ≤ H3.toNat) (o4 : H3.toNat ≤ H4.toNat) (o5 : H4.toNat ≤ H5.toNat) (o6 : H5.toNat ≤ H6.toNat) :
    ∀ c, AdC.live ∅ c → ∀ x, adRgs H H1 H2 H3 H4 H5 H6 c x → H.toNat ≤ x.toNat ∧ x.toNat < H6.toNat := by
  intro c hc x hx
  cases c <;> (simp only [adRgs] at hx <;> omega)

/-- Final assembly of `bal_ensure_account`: the fresh record at `H` with its five components in consecutive fresh
intervals, and `bal_accounts` set to include it. -/
theorem balEnsure_final {D : BitVec 64 → Prop} {B : Bool} {BA IA IS KB : BitVec 64} {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H Nj : BitVec 64} {M1 : Mem} (bw : BalW D B BA IA IS KB ADs Rg H M1)
    {H1 H2 T8 H3 L16 H4 L24 H5 L32 H6 : BitVec 64}
    (o1 : H.toNat + 40 ≤ H1.toNat) (o2 : H1.toNat ≤ H2.toNat) (o3 : H2.toNat ≤ H3.toNat) (o4 : H3.toNat ≤ H4.toNat)
    (o5 : H4.toNat ≤ H5.toNat) (o6 : H5.toNat ≤ H6.toNat) (hb6 : H6.toNat ≤ 33806089496)
    {M9 : Mem} (fr9 : ∀ x, x.toNat < H.toNat → M9 x = M1 x)
    (c0 : M9 (H + 0#64) = .word H1) (c8 : M9 (H + 8#64) = .word T8) (c16 : M9 (H + 16#64) = .word L16)
    (c24 : M9 (H + 24#64) = .word L24) (c32 : M9 (H + 32#64) = .word L32)
    (v0 : CompV D B 0 H1 H1 H2 H6 M9) (v1 : CompV D B 1 T8 H2 H3 H6 M9) (v2 : CompV D B 2 L16 H3 H4 H6 M9)
    (v3 : CompV D B 3 L24 H4 H5 H6 M9) (v4 : CompV D B 4 L32 H5 H6 H6 M9)
    {lba : TLay} (klba : lba.KL = 20#64) (sdba : lba.SD.toNat ≤ 56) (hbaPh : ∀ x, TabPhys BA lba x → Rg .ba x)
    {Mf : Mem} {Gf : GA} (frs : ∀ x, ¬ TabPhys BA lba x → x.toNat < H6.toNat → Mf x = M9 x)
    (srv : SetRV D B BA lba H6 (insert H ADs) Mf Gf)
    (hn : Gf.lookup (ofString "journal_n") = some (.val (.word Nj))) :
    BalStepA D B BA IA IS KB ADs Rg H Nj M1 H Mf Gf := by
  obtain ⟨l',Hp,hHp,le,rv',ekl,esd,ph⟩ := srv
  obtain ⟨bv,dis,bl⟩ := bw
  have eHk : ∀ k : Nat, k < 40 → (H + BitVec.ofNat 64 k).toNat = H.toNat + k := fun k hk => by
    rw [BitVec.toNat_add]; simp; omega
  have nBA : ∀ x, x.toNat < H.toNat → ¬ TabPhys BA lba x → Mf x = M1 x := fun x hx hb =>
    (frs x hb (by omega)).trans (fr9 x hx)
  have baLt : ∀ x, TabPhys BA lba x → x.toNat < H.toNat := fun x hx => bl .ba trivial x (hbaPh x hx)
  have keepOld : ∀ c, BalK.live ADs c → c ≠ .ba → ∀ x, Rg c x → Mf x = M1 x := fun c hc ne x hx =>
    nBA x (bl c hc x hx) (fun h => dis .ba c trivial hc (Ne.symm ne) x (hbaPh x h) hx)
  have keepNew : ∀ x, H.toNat ≤ x.toNat → x.toNat < H6.toNat → Mf x = M9 x := fun x l u =>
    frs x (fun h => by have := baLt x h; omega) u
  have nH : H ∉ ADs := fun h => by
    obtain ⟨_,_,_,_,_,_,RgA,_,_,_,hrw,_,_,_,_,_,_,_,inO⟩ := bv (.ad H) h
    have := bl (.ad H) h H (inO .recw trivial H (hrw H (Or.inl rfl))); omega
  have newAd : AdO D B (fun x => H.toNat ≤ x.toNat ∧ x.toNat < H6.toNat) H Hp Mf := by
    obtain ⟨Hl0,rv0,hl0,ph0⟩ := v0
    have a0 : H + 0#64 = H := by simp
    refine ⟨H1,T8,L16,L24,L32,∅,adRgs H H1 H2 H3 H4 H5 H6,newLay H1 32#64 8#64 3,Hl0,⟨?_,?_,?_,?_,?_⟩,fun x hx => ?_,
      ⟨tabRV_frame rv0 (fun x hx => keepNew x (by obtain ⟨h1,_⟩ := ph0 x hx; omega)
        (by obtain ⟨_,h2⟩ := ph0 x hx; omega)),
        by omega,rfl,by show (allocationEnd 0 (32#64)).toNat ≤ 56; decide,fun x hx => ph0 x hx⟩,
      tabO_mono (tabO_frame v1 (fun x ⟨h1,h2⟩ => keepNew x (by omega) (by omega))) (by omega),
      lstO_frame v2 (fun x ⟨h1,h2⟩ => keepNew x (by omega) (by omega)),
      lstO_frame v3 (fun x ⟨h1,h2⟩ => keepNew x (by omega) (by omega)),
      lstO_frame v4 (fun x ⟨h1,h2⟩ => keepNew x (by omega) (by omega)),fun l hl => absurd hl (by simp),
      adRgs_dis o1 o2 o3 o4 o5,adRgs_in o1 o2 o3 o4 o5 o6⟩
    · rw [keepNew H (le_refl _) (by omega),← a0,c0]
    · rw [keepNew _ (by rw [eHk 8 (by omega)]; omega) (by rw [eHk 8 (by omega)]; omega)]; exact c8
    · rw [keepNew _ (by rw [eHk 16 (by omega)]; omega) (by rw [eHk 16 (by omega)]; omega)]; exact c16
    · rw [keepNew _ (by rw [eHk 24 (by omega)]; omega) (by rw [eHk 24 (by omega)]; omega)]; exact c24
    · rw [keepNew _ (by rw [eHk 32 (by omega)]; omega) (by rw [eHk 32 (by omega)]; omega)]; exact c32
    · show H.toNat ≤ x.toNat ∧ x.toNat < H.toNat + 40
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · omega
      · rw [eHk 8 (by omega)]; omega
      · rw [eHk 16 (by omega)]; omega
      · rw [eHk 24 (by omega)]; omega
      · rw [eHk 32 (by omega)]; omega
  refine ⟨insert H ADs,fun c x => (BalK.live ADs c ∧ Rg c x) ∨ (c = .ba ∧ H6.toNat ≤ x.toNat ∧ x.toNat < Hp.toNat) ∨
      (c = .ad H ∧ H.toNat ≤ x.toNat ∧ x.toNat < H6.toNat),Hp,hHp,by omega,hn,
    ⟨fun c hc => ?_,fun c c' hc hc' ne x h1 h2 => ?_,fun c hc x hx => ?_⟩,fun _ h => Or.inr h,fun c hc x hx => ?_,
    fun x hx hn' => nBA x hx (fun h => hn' .ba trivial (hbaPh x h)),Set.mem_insert _ _⟩
  · have old : ∀ c, BalK.live ADs c → c ≠ .ba → BalV D B BA IA IS KB (insert H ADs) c
        (fun x => (BalK.live ADs c ∧ Rg c x) ∨ (c = .ba ∧ H6.toNat ≤ x.toNat ∧ x.toNat < Hp.toNat) ∨
          (c = .ad H ∧ H.toNat ≤ x.toNat ∧ x.toNat < H6.toNat)) Hp Mf := fun c hc ne =>
      balV_sub c (balV_mono c (balV_values c (balV_frame c (bv c hc) (keepOld c hc ne)) (fun t ht => Or.inr ht))
        (by omega)) (fun x h => Or.inl ⟨hc,h⟩)
    cases c with
    | ba =>
      exact ⟨l',Hp,rv',le_refl _,by rw [ekl]; exact klba,by rw [esd]; exact sdba,fun x hx => by
        rcases ph x hx with h | ⟨h1,h2⟩
        · exact Or.inl ⟨trivial,hbaPh x h⟩
        · exact Or.inr (Or.inl ⟨rfl,h1,h2⟩)⟩
    | ia => exact old .ia trivial (by decide)
    | is => exact old .is trivial (by decide)
    | kb => exact old .kb trivial (by decide)
    | ad a =>
      rcases hc with rfl | ha
      · exact adO_sub (adO_mono newAd (le_refl _)) (fun x h => Or.inr (Or.inr ⟨rfl,h⟩))
      · exact old (.ad a) ha (by simp)
  · rcases h1 with ⟨l1,h1⟩ | ⟨e1,a1,b1⟩ | ⟨e1,a1,b1⟩ <;> rcases h2 with ⟨l2,h2⟩ | ⟨e2,a2,b2⟩ | ⟨e2,a2,b2⟩
    · exact dis c c' l1 l2 ne x h1 h2
    · have := bl c l1 x h1; omega
    · have := bl c l1 x h1; omega
    · have := bl c' l2 x h2; omega
    · exact ne (e1.trans e2.symm)
    · omega
    · have := bl c' l2 x h2; omega
    · omega
    · exact ne (e1.trans e2.symm)
  · rcases hx with ⟨l1,h1⟩ | ⟨_,_,b1⟩ | ⟨_,_,b1⟩
    · have := bl c l1 x h1; omega
    · exact b1
    · omega
  · rcases hx with ⟨l1,h1⟩ | ⟨_,a1,b1⟩ | ⟨_,a1,b1⟩
    · exact Or.inl ⟨l1,h1⟩
    · exact Or.inr ⟨by omega,b1⟩
    · exact Or.inr ⟨a1,by omega⟩

theorem tabO_of_tabV {Tt A P : BitVec 64} {M : Mem} (h : TabV Tt A P M) (hT : Tt.toNat + 72 ≤ P.toNat) :
    TabO (fun x => A.toNat ≤ x.toNat ∧ x.toNat < P.toNat) Tt P M := by
  obtain ⟨KL,SD,C,N,KS,VS,US,OS,OPS,b,lay,hd,a,li⟩ := h
  exact ⟨⟨KL,SD,C,N,KS,VS,US,OS,OPS,b⟩,lay,hd,fun x lo hi => ⟨by omega,by omega⟩,li⟩

theorem lstO_of_lnew {E Cp H X H' : BitVec 64} {M1 M' : Mem} {G' : GA} (h : LNew E Cp H M1 X H' M' G')
    (hC : 0 < Cp.toNat) (hEC : (E * Cp).toNat = E.toNat * Cp.toNat) :
    LstO E (fun x => H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat) X M' := by
  obtain ⟨hX,⟨Pp,hXP,hd,hP⟩,_,_,_⟩ := h
  rw [hEC] at hP
  have e8 : (X + 8#64).toNat = X.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have e16 : (X + 16#64).toNat = X.toNat + 16 := by rw [BitVec.toNat_add]; simp; omega
  refine ⟨Pp,0#64,Cp,hd,by simp,hC,hXP,fun x hx => ?_,fun x l u => ⟨⟨by omega,by omega⟩,fun hx => ?_⟩⟩
  · rcases hx with rfl | rfl | rfl
    · exact ⟨hX,by omega⟩
    · rw [e8]; exact ⟨by omega,by omega⟩
    · rw [e16]; exact ⟨by omega,by omega⟩
  · rcases hx with rfl | rfl | rfl
    · omega
    · rw [e8] at l; omega
    · rw [e16] at l; omega

section be
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `bal_ensure_account(addr)` body. -/
theorem balEnsure_aqgd (bk : BalKeep) (BA IA IS KB Ix A : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop)
    (H Nj : BitVec 64) (M1 : Mem) (G1 : GA) (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => ∃ ad : BitVec 64, v = .val (.word ad) ∧ BalStepA D B BA IA IS KB ADs Rg H Nj M1 ad M G)
      (sourceFunctionBody Guest.guestFn_bal_ensure_account) := by
  refine aqgd_of_arenaFact (Φ := H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
    (fun _ _ g aw ⟨_,_,hg⟩ => by
      rw [hg] at aw
      exact ⟨(jws_heap_facts aw.1.1.1 hH1).2.1,(jws_heap_facts aw.1.1.1 hH1).2.2⟩) ?_
  intro ⟨hHE,hal⟩
  have gba := hB1.1
  obtain ⟨lba,Hl,rvba,hHl,klba,sdba,phba⟩ := bw.1 .ba trivial
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_bal_ensure_account,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  refine aqgd_decCall_htabGet_b bk BA IA IS KB Ix (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)))
    (Pc := fun L M G => (L.lookup (ofString "addr") = some (.val (.word A)) ∧ ∃ p val : BitVec 64,
      L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ (p ≠ 0 → val ∈ ADs)) ∧
      M = M1 ∧ G = G1)
    (Qc := fun _ _ _ => False) (ofString "m") _ _ BA A Hl H lba ADs M1 G1 rvba hH1 hHl hB1 Dall (Or.inl klba) hK hKE ?_
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ hg la
    have gb : s.globals.lookup (ofString "bal_accounts") = some (.val (.word BA)) := by rw [hg]; exact gba
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la,gb]
  · intro L p val la _ prop
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact la,p,val,lookup_update_eq' _ _ _,prop⟩,rfl,rfl⟩
  refine aqgd_seq (Q := fun L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧ M = M1 ∧ G = G1)
    (aqgd_ite (CT := fun L _ _ => ∃ p val : BitVec 64,
        L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ p ≠ 0)
      (CF := fun _ _ _ => True) _ ?_ ?_ ?_) ?_
  · intro F s x H' _ _ ⟨⟨_,p,val,hm,_⟩,_,_⟩ _ ev
    refine ⟨fun hx => ⟨p,val,hm,fun hp => hx ?_⟩,fun _ => trivial⟩
    subst hp
    simp [EV,evalHOLExact,hm,Compiler.Encoders.Asm.wordCmpHOL] at ev
    exact ev.symm
  · refine aqgd_return _ (fun s v H' _ hG ⟨⟨⟨_,p,val,hm,prop⟩,hM,hG1⟩,⟨p',val',hm',hp'⟩⟩ _ ev => ?_)
    rw [hm] at hm'
    simp only [Option.some.injEq,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,
      HolWordLab.word.injEq,and_true] at hm'
    obtain ⟨rfl,rfl⟩ := hm'
    simp [EV,evalHOLExact,hm] at ev
    subst ev
    unfold GIs at hG
    have e : s.globals = G1 := by rw [hG]; exact hG1
    first | rw [hM,e] | rw [hM,hG1]
    exact ⟨val,rfl,ADs,Rg,H,hH1,le_refl _,hn1,bw,fun _ h => h,fun c hc x hx => Or.inl ⟨hc,hx⟩,fun _ _ _ => rfl,
      prop hp'⟩
  · exact aqgd_conseq aqgd_skip (fun _ _ _ h => ⟨h.1.1.1,h.1.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have hwH : w.toNat < H.toNat := by omega
  -- ad = alloc(40)
  refine aqgd_decCall_alloc_b bk BA IA IS KB Ix (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)))
    (Pc := fun L M G => ((L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H))) ∧ M = M1) ∧ ∃ H1 : BitVec 64, HeapIs G H1 ∧
      H.toNat + 40 ≤ H1.toNat ∧ H1.toNat ≤ 33806089496 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      BalG BA IA IS KB Ix G)
    (Qc := fun _ _ _ => False) (ofString "ad") 40#64 H Nj M1 G1 hH1 hn1 hB1 ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro L H1 G' la hH' c1 c2 _ hn' bg
    exact ⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact la,lookup_update_eq' _ _ _⟩,rfl⟩,H1,hH',by simpa using c1,
      c2,hn',bg⟩
  -- t = htab_new(32, 8)
  refine aqgd_ghostR (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H)))
    (P := fun M G => M = M1 ∧ ∃ H1 : BitVec 64, HeapIs G H1 ∧ H.toNat + 40 ≤ H1.toNat ∧ H1.toNat ≤ 33806089496 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G)
    (fun M2 G2 ⟨hM2,H1,hH,c1,c2,hn,bg⟩ => ?_) |> fun h => aqgd_conseq h
      (fun L M G ⟨⟨⟨la,lad⟩,hM⟩,rest⟩ => ⟨⟨la,lad⟩,hM,rest⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have hwH1 : w.toNat < H1.toNat := by omega
  refine aqgd_decCall_htabNew_b bk BA IA IS KB Ix (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H)))
    (Pc := fun L M G => ∃ H2 : BitVec 64, ((L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H)) ∧ L.lookup (ofString "t") = some (.val (.word H1))) ∧
      (∀ x, x.toNat < H1.toNat → M x = M1 x) ∧ CompV D B 0 H1 H1 H2 H2 M) ∧ HeapIs G H2 ∧
      H1.toNat + 72 ≤ H2.toNat ∧ H2.toNat ≤ 33806089496 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      BalG BA IA IS KB Ix G)
    (Qc := fun _ _ _ => False) (ofString "t") 32#64 8#64 3 H1 Nj M2 G2 hH hn bg hwH1 (by decide) (by decide)
    (by decide) Dall ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro L H2 M' G' ⟨la,lad⟩ fr hH2 hT hE nt rv hn' bg'
    obtain ⟨hl2,ph⟩ := newRV_loc nt rv rfl
    exact ⟨H2,⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact la,by rw [lookup_update_ne' _ _ (by decide)]; exact lad,
      lookup_update_eq' _ _ _⟩,fun x hx => by rw [fr x hx,hM2],_,rv,hl2,ph⟩,hH2,hT,hE,hn',bg'⟩
  -- st ad + 0, t
  have hwHk : ∀ k : Nat, k < 40 → w ≠ H + BitVec.ofNat 64 k := fun k hk e => by
    have : (H + BitVec.ofNat 64 k).toNat = H.toNat + k := by rw [BitVec.toNat_add]; simp; omega
    rw [← e] at this; omega
  have eHk : ∀ k : Nat, k < 40 → (H + BitVec.ofNat 64 k).toNat = H.toNat + k := fun k hk => by
    rw [BitVec.toNat_add]; simp; omega
  refine aqgd_seq (aqgd_storeW (Q := fun L M G => ∃ H2 : BitVec 64, ((L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H)) ∧ L.lookup (ofString "t") = some (.val (.word H1))) ∧
      (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ CompV D B 0 H1 H1 H2 H2 M) ∧ HeapIs G H2 ∧
      H1.toNat + 72 ≤ H2.toNat ∧ H2.toNat ≤ 33806089496 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      BalG BA IA IS KB Ix G) _ _ (fun s _ _ ⟨H2,⟨⟨la,lad,lt⟩,fr,cv⟩,rest⟩ => ⟨H + 0#64,H1,
        by simp [EV,evalHOLExact,evalListHOLExact,lad,wordOpHOL,wordOp,valueIsWord,valueWord],
        by simp [EV,evalHOLExact,lt],hwHk 0 (by omega),H2,⟨⟨la,lad,lt⟩,fun x hx => ?_,by simp,
        compV_frame cv (fun x l u => ?_)⟩,rest⟩)) ?_
  · have : x ≠ H + 0#64 := fun e => by rw [e,eHk 0 (by omega)] at hx; omega
    simp only [if_neg this]; exact (fr x (by omega))
  · have : x ≠ H + 0#64 := fun e => by rw [e,eHk 0 (by omega)] at l; omega
    simp only [if_neg this]
  -- t = htab_new(32, 8)
  refine aqgd_seq (Q := fun L M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64,
      ((L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "ad") = some (.val (.word H)) ∧
        L.lookup (ofString "t") = some (.val (.word q.2.1))) ∧
      (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ CompV D B 0 H1 H1 q.1 q.2.2 M ∧
        CompV D B 1 q.2.1 q.1 q.2.2 q.2.2 M) ∧ HeapIs G q.2.2 ∧ H1.toNat + 72 ≤ q.1.toNat ∧ q.1.toNat ≤ q.2.2.toNat ∧
      q.2.2.toNat ≤ 33806089496 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      BalG BA IA IS KB Ix G) ?_ ?_
  · refine aqgd_conseq (P := fun L M G => (fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
        L.lookup (ofString "ad") = some (.val (.word H))) L ∧ (fun M G => ∃ H2 : BitVec 64,
        ((∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ CompV D B 0 H1 H1 H2 H2 M) ∧
        HeapIs G H2 ∧ H1.toNat + 72 ≤ H2.toNat ∧ H2.toNat ≤ 33806089496 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G) M G)
      (aqgd_ghostR (fun M3 G3 ⟨H2,⟨fr,c0,cv⟩,hH,h12,hb2,hn,bg⟩ => ?_))
      (fun L M G ⟨H2,⟨⟨la,lad,_⟩,fr,c0,cv⟩,rest⟩ => ⟨⟨la,lad⟩,H2,⟨fr,c0,cv⟩,rest⟩) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
        (by simp [balWatched,keepsG,goodBal,balExtra])
        (aqgd_callAssign_htabNew (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
          L.lookup (ofString "ad") = some (.val (.word H))) (ofString "t") 32#64 8#64 H2 Nj M3 G3 hH hn (by omega)))
      (fun L M G ⟨⟨la,lad⟩,hM,hG⟩ => ⟨⟨⟨la,lad⟩,hM,hG⟩,by rw [hG]; exact bg⟩) ?_ (fun _ _ _ h => h.1)
    intro L M G ⟨⟨L0,Tt,H3,eL,⟨la,lad⟩,hHT,fr',hH3,hT,hE,nt,hn'⟩,bg'⟩
    subst eL
    have tv : TabV Tt H2 H3 M := tabV_ofNew (b := 3) nt hT hE hHT (by decide) (by decide) (by decide) (by decide)
      (by decide)
    refine ⟨(H2,Tt,H3),?_⟩
    dsimp only
    exact ⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact la,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lad,lookup_update_eq' _ _ _⟩,
      fun x hx => by rw [fr' x (by omega),fr x hx],by rw [fr' _ (by rw [eHk 0 (by omega)]; omega),c0],
      compV_mono (compV_frame cv (fun x l u => fr' x u)) (by omega),tabO_of_tabV tv (by omega)⟩,
      hH3,h12,by omega,hE,hn',bg'⟩
  -- st ad + 8, t
  refine aqgd_seq (aqgd_storeW (Q := fun L M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64,
      ((L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "ad") = some (.val (.word H))) ∧
      (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word q.2.1 ∧
        CompV D B 0 H1 H1 q.1 q.2.2 M ∧ CompV D B 1 q.2.1 q.1 q.2.2 q.2.2 M) ∧ HeapIs G q.2.2 ∧
      H1.toNat + 72 ≤ q.1.toNat ∧ q.1.toNat ≤ q.2.2.toNat ∧
      q.2.2.toNat ≤ 33806089496 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      BalG BA IA IS KB Ix G) _ _ (fun s _ _ ⟨q,⟨⟨la,lad,lt⟩,fr,c0,cv0,cv1⟩,hH,h12,h23,rest⟩ => ⟨H + 8#64,q.2.1,
        by simp [EV,evalHOLExact,evalListHOLExact,lad,wordOpHOL,wordOp,valueIsWord,valueWord],
        by simp [EV,evalHOLExact,lt],hwHk 8 (by omega),q,⟨⟨la,lad⟩,fun x hx => ?_,?_,by simp,
        compV_frame cv0 (fun x l u => ?_),compV_frame cv1 (fun x l u => ?_)⟩,hH,h12,h23,rest⟩)) ?_
  · have : x ≠ H + 8#64 := fun e => by rw [e,eHk 8 (by omega)] at hx; omega
    simp only [if_neg this]; exact (fr x hx)
  · have : H + 0#64 ≠ H + 8#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 0 (by omega),eHk 8 (by omega)] at this; omega
    simp only [if_neg this]; exact c0
  · have : x ≠ H + 8#64 := fun e => by rw [e,eHk 8 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 8#64 := fun e => by rw [e,eHk 8 (by omega)] at l; omega
    simp only [if_neg this]
  -- l = lst_new(40, 4)
  refine aqgd_conseq (P := fun L M G => (fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H))) L ∧ (fun M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64,
      ((∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word q.2.1 ∧
        CompV D B 0 H1 H1 q.1 q.2.2 M ∧ CompV D B 1 q.2.1 q.1 q.2.2 q.2.2 M) ∧ HeapIs G q.2.2 ∧
      H1.toNat + 72 ≤ q.1.toNat ∧ q.1.toNat ≤ q.2.2.toNat ∧ q.2.2.toNat ≤ 33806089496 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G) M G)
    (aqgd_ghostR (fun M4 G4 ⟨q,⟨fr,c0,c8,cv0,cv1⟩,hH,h12,h23,hb,hn,bg⟩ => ?_))
    (fun L M G ⟨q,⟨⟨la,lad⟩,rest⟩,rest2⟩ => ⟨⟨la,lad⟩,q,rest,rest2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨H2,T8,H3⟩
  dsimp only at fr c0 c8 cv0 cv1 hH h12 h23 hb
  refine aqgd_decCall_lstNew_b bk BA IA IS KB Ix (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H)))
    (Pc := fun L M G => ∃ H4 L16 : BitVec 64, ((L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H)) ∧ L.lookup (ofString "l") = some (.val (.word L16))) ∧
      (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word T8 ∧
        CompV D B 0 H1 H1 H2 H4 M ∧ CompV D B 1 T8 H2 H3 H4 M ∧ CompV D B 2 L16 H3 H4 H4 M) ∧ HeapIs G H4 ∧
      H3.toNat ≤ H4.toNat ∧ H4.toNat ≤ 33806089496 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      BalG BA IA IS KB Ix G)
    (Qc := fun _ _ _ => False) (ofString "l") 40#64 4#64 H3 Nj M4 G4 hH hn bg (by omega) ?_ ?_
    (fun _ _ _ _ _ h => h.elim)
  · intro L X H4 M' G' ⟨la,lad⟩ ln hn' bg'
    have ln' := ln
    obtain ⟨hX,⟨Pp,hXP,_,hP⟩,hH4,hE4,fr'⟩ := ln'
    have e160 : ((40#64) * (4#64)).toNat = 160 := by decide
    rw [e160] at hP
    refine ⟨H4,X,⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact la,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lad,lookup_update_eq' _ _ _⟩,
      fun x hx => by rw [fr' x (by omega),fr x hx],by rw [fr' _ (by rw [eHk 0 (by omega)]; omega),c0],
      by rw [fr' _ (by rw [eHk 8 (by omega)]; omega),c8],
      compV_mono (compV_frame cv0 (fun x l u => fr' x (by omega))) (by omega),
      compV_mono (compV_frame cv1 (fun x l u => fr' x u)) (by omega),
      lstO_of_lnew ln (by decide) (by decide)⟩,hH4,by omega,hE4,hn',bg'⟩
  -- st ad + 16, l
  refine aqgd_seq (aqgd_storeW (Q := fun L M G => ∃ H4 L16 : BitVec 64,
      ((L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "ad") = some (.val (.word H))) ∧
      (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word T8 ∧
        M (H + 16#64) = .word L16 ∧
        CompV D B 0 H1 H1 H2 H4 M ∧ CompV D B 1 T8 H2 H3 H4 M ∧ CompV D B 2 L16 H3 H4 H4 M) ∧ HeapIs G H4 ∧
      H3.toNat ≤ H4.toNat ∧ H4.toNat ≤ 33806089496 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      BalG BA IA IS KB Ix G) _ _ (fun s _ _ ⟨H4,L16,⟨⟨la,lad,ll⟩,fr4,c0',c8',cv0',cv1',cv2'⟩,rest⟩ => ⟨H + 16#64,L16,
        by simp [EV,evalHOLExact,evalListHOLExact,lad,wordOpHOL,wordOp,valueIsWord,valueWord],
        by simp [EV,evalHOLExact,ll],hwHk 16 (by omega),H4,L16,⟨⟨la,lad⟩,fun x hx => ?_,?_,?_,by simp,
        compV_frame cv0' (fun x l u => ?_),compV_frame cv1' (fun x l u => ?_),compV_frame cv2' (fun x l u => ?_)⟩,
        rest⟩)) ?_
  · have : x ≠ H + 16#64 := fun e => by rw [e,eHk 16 (by omega)] at hx; omega
    simp only [if_neg this]; exact (fr4 x hx)
  · have : H + 0#64 ≠ H + 16#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 0 (by omega),eHk 16 (by omega)] at this; omega
    simp only [if_neg this]; exact c0'
  · have : H + 8#64 ≠ H + 16#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 8 (by omega),eHk 16 (by omega)] at this; omega
    simp only [if_neg this]; exact c8'
  · have : x ≠ H + 16#64 := fun e => by rw [e,eHk 16 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 16#64 := fun e => by rw [e,eHk 16 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 16#64 := fun e => by rw [e,eHk 16 (by omega)] at l; omega
    simp only [if_neg this]
  -- l = lst_new(16, 4)
  refine aqgd_seq (Q := fun L M G => ∃ H4 L16 H5 L24 : BitVec 64,
      ((L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "ad") = some (.val (.word H)) ∧
        L.lookup (ofString "l") = some (.val (.word L24))) ∧
      (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word T8 ∧
        M (H + 16#64) = .word L16 ∧ CompV D B 0 H1 H1 H2 H5 M ∧ CompV D B 1 T8 H2 H3 H5 M ∧
        CompV D B 2 L16 H3 H4 H5 M ∧ CompV D B 3 L24 H4 H5 H5 M) ∧ HeapIs G H5 ∧
      H3.toNat ≤ H4.toNat ∧ H4.toNat ≤ H5.toNat ∧ H5.toNat ≤ 33806089496 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G) ?_ ?_
  · refine aqgd_conseq (P := fun L M G => (fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
        L.lookup (ofString "ad") = some (.val (.word H))) L ∧ (fun M G => ∃ H4 L16 : BitVec 64,
        ((∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word T8 ∧
          M (H + 16#64) = .word L16 ∧
          CompV D B 0 H1 H1 H2 H4 M ∧ CompV D B 1 T8 H2 H3 H4 M ∧ CompV D B 2 L16 H3 H4 H4 M) ∧ HeapIs G H4 ∧
        H3.toNat ≤ H4.toNat ∧ H4.toNat ≤ 33806089496 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        BalG BA IA IS KB Ix G) M G)
      (aqgd_ghostR (fun M5 G5 ⟨H4,L16,⟨fr4,c0',c8',c16',cv0',cv1',cv2'⟩,hH4,h34,hb4,hn4,bg4⟩ => ?_))
      (fun L M G ⟨H4,L16,⟨⟨la,lad⟩,rest⟩,rest2⟩ => ⟨⟨la,lad⟩,H4,L16,rest,rest2⟩) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
        (by simp [balWatched,keepsG,goodBal,balExtra])
        (aqgd_callAssign_lstNew_g (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
          L.lookup (ofString "ad") = some (.val (.word H))) (ofString "l") 16#64 4#64 H4 Nj M5 G5 hH4 hn4 (by omega)))
      (fun L M G ⟨⟨la,lad⟩,hM,hG⟩ => ⟨⟨⟨la,lad⟩,hM,hG⟩,by rw [hG]; exact bg4⟩) ?_ (fun _ _ _ h => h.1)
    intro L M G ⟨⟨L0,X,H5,eL,⟨la,lad⟩,ln,hn'⟩,bg'⟩
    subst eL
    have ln' := ln
    obtain ⟨hX,⟨Pp,hXP,_,hP⟩,hH5,hE5,fr'⟩ := ln'
    have e64 : ((16#64) * (4#64)).toNat = 64 := by decide
    rw [e64] at hP
    exact ⟨H4,L16,H5,X,⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact la,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lad,lookup_update_eq' _ _ _⟩,
      fun x hx => by rw [fr' x (by omega),fr4 x hx],by rw [fr' _ (by rw [eHk 0 (by omega)]; omega),c0'],
      by rw [fr' _ (by rw [eHk 8 (by omega)]; omega),c8'],by rw [fr' _ (by rw [eHk 16 (by omega)]; omega),c16'],
      compV_mono (compV_frame cv0' (fun x l u => fr' x (by omega))) (by omega),
      compV_mono (compV_frame cv1' (fun x l u => fr' x (by omega))) (by omega),
      compV_mono (compV_frame cv2' (fun x l u => fr' x u)) (by omega),
      lstO_of_lnew ln (by decide) (by decide)⟩,hH5,h34,by omega,hE5,hn',bg'⟩
  -- st ad + 24, l
  refine aqgd_seq (aqgd_storeW (Q := fun L M G => ∃ H4 L16 H5 L24 : BitVec 64,
      ((L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "ad") = some (.val (.word H))) ∧
      (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word T8 ∧
        M (H + 16#64) = .word L16 ∧ M (H + 24#64) = .word L24 ∧ CompV D B 0 H1 H1 H2 H5 M ∧
        CompV D B 1 T8 H2 H3 H5 M ∧ CompV D B 2 L16 H3 H4 H5 M ∧ CompV D B 3 L24 H4 H5 H5 M) ∧ HeapIs G H5 ∧
      H3.toNat ≤ H4.toNat ∧ H4.toNat ≤ H5.toNat ∧ H5.toNat ≤ 33806089496 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G) _ _
      (fun s _ _ ⟨H4,L16,H5,L24,⟨⟨la,lad,ll⟩,fr5,c0',c8',c16',cv0',cv1',cv2',cv3'⟩,rest⟩ => ⟨H + 24#64,L24,
        by simp [EV,evalHOLExact,evalListHOLExact,lad,wordOpHOL,wordOp,valueIsWord,valueWord],
        by simp [EV,evalHOLExact,ll],hwHk 24 (by omega),H4,L16,H5,L24,⟨⟨la,lad⟩,fun x hx => ?_,?_,?_,?_,by simp,
        compV_frame cv0' (fun x l u => ?_),compV_frame cv1' (fun x l u => ?_),compV_frame cv2' (fun x l u => ?_),
        compV_frame cv3' (fun x l u => ?_)⟩,rest⟩)) ?_
  · have : x ≠ H + 24#64 := fun e => by rw [e,eHk 24 (by omega)] at hx; omega
    simp only [if_neg this]; exact (fr5 x hx)
  · have : H + 0#64 ≠ H + 24#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 0 (by omega),eHk 24 (by omega)] at this; omega
    simp only [if_neg this]; exact c0'
  · have : H + 8#64 ≠ H + 24#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 8 (by omega),eHk 24 (by omega)] at this; omega
    simp only [if_neg this]; exact c8'
  · have : H + 16#64 ≠ H + 24#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 16 (by omega),eHk 24 (by omega)] at this; omega
    simp only [if_neg this]; exact c16'
  · have : x ≠ H + 24#64 := fun e => by rw [e,eHk 24 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 24#64 := fun e => by rw [e,eHk 24 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 24#64 := fun e => by rw [e,eHk 24 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 24#64 := fun e => by rw [e,eHk 24 (by omega)] at l; omega
    simp only [if_neg this]
  -- l = lst_new(24, 2)
  refine aqgd_seq (Q := fun L M G => ∃ H4 L16 H5 L24 H6 L32 : BitVec 64,
      ((L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "ad") = some (.val (.word H)) ∧
        L.lookup (ofString "l") = some (.val (.word L32))) ∧
      (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word T8 ∧
        M (H + 16#64) = .word L16 ∧ M (H + 24#64) = .word L24 ∧ CompV D B 0 H1 H1 H2 H6 M ∧
        CompV D B 1 T8 H2 H3 H6 M ∧ CompV D B 2 L16 H3 H4 H6 M ∧ CompV D B 3 L24 H4 H5 H6 M ∧
        CompV D B 4 L32 H5 H6 H6 M) ∧ HeapIs G H6 ∧
      H3.toNat ≤ H4.toNat ∧ H4.toNat ≤ H5.toNat ∧ H5.toNat ≤ H6.toNat ∧ H6.toNat ≤ 33806089496 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G) ?_ ?_
  · refine aqgd_conseq (P := fun L M G => (fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
        L.lookup (ofString "ad") = some (.val (.word H))) L ∧ (fun M G => ∃ H4 L16 H5 L24 : BitVec 64,
        ((∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word T8 ∧
          M (H + 16#64) = .word L16 ∧ M (H + 24#64) = .word L24 ∧ CompV D B 0 H1 H1 H2 H5 M ∧
          CompV D B 1 T8 H2 H3 H5 M ∧ CompV D B 2 L16 H3 H4 H5 M ∧ CompV D B 3 L24 H4 H5 H5 M) ∧ HeapIs G H5 ∧
        H3.toNat ≤ H4.toNat ∧ H4.toNat ≤ H5.toNat ∧ H5.toNat ≤ 33806089496 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G) M G)
      (aqgd_ghostR (fun M6 G6 ⟨H4,L16,H5,L24,⟨fr5,c0',c8',c16',c24',cv0',cv1',cv2',cv3'⟩,hH5,h34,h45,hb5,hn5,bg5⟩ => ?_))
      (fun L M G ⟨H4,L16,H5,L24,⟨⟨la,lad⟩,rest⟩,rest2⟩ => ⟨⟨la,lad⟩,H4,L16,H5,L24,rest,rest2⟩) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
        (by simp [balWatched,keepsG,goodBal,balExtra])
        (aqgd_callAssign_lstNew_g (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
          L.lookup (ofString "ad") = some (.val (.word H))) (ofString "l") 24#64 2#64 H5 Nj M6 G6 hH5 hn5 (by omega)))
      (fun L M G ⟨⟨la,lad⟩,hM,hG⟩ => ⟨⟨⟨la,lad⟩,hM,hG⟩,by rw [hG]; exact bg5⟩) ?_ (fun _ _ _ h => h.1)
    intro L M G ⟨⟨L0,X,H6,eL,⟨la,lad⟩,ln,hn'⟩,bg'⟩
    subst eL
    have ln' := ln
    obtain ⟨hX,⟨Pp,hXP,_,hP⟩,hH6,hE6,fr'⟩ := ln'
    have e48 : ((24#64) * (2#64)).toNat = 48 := by decide
    rw [e48] at hP
    exact ⟨H4,L16,H5,L24,H6,X,⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact la,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lad,lookup_update_eq' _ _ _⟩,
      fun x hx => by rw [fr' x (by omega),fr5 x hx],by rw [fr' _ (by rw [eHk 0 (by omega)]; omega),c0'],
      by rw [fr' _ (by rw [eHk 8 (by omega)]; omega),c8'],by rw [fr' _ (by rw [eHk 16 (by omega)]; omega),c16'],
      by rw [fr' _ (by rw [eHk 24 (by omega)]; omega),c24'],
      compV_mono (compV_frame cv0' (fun x l u => fr' x (by omega))) (by omega),
      compV_mono (compV_frame cv1' (fun x l u => fr' x (by omega))) (by omega),
      compV_mono (compV_frame cv2' (fun x l u => fr' x (by omega))) (by omega),
      compV_mono (compV_frame cv3' (fun x l u => fr' x u)) (by omega),
      lstO_of_lnew ln (by decide) (by decide)⟩,hH6,h34,h45,by omega,hE6,hn',bg'⟩
  -- st ad + 32, l
  refine aqgd_seq (aqgd_storeW (Q := fun L M G => ∃ H4 L16 H5 L24 H6 L32 : BitVec 64,
      ((L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "ad") = some (.val (.word H))) ∧
      (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word T8 ∧
        M (H + 16#64) = .word L16 ∧ M (H + 24#64) = .word L24 ∧ M (H + 32#64) = .word L32 ∧
        CompV D B 0 H1 H1 H2 H6 M ∧ CompV D B 1 T8 H2 H3 H6 M ∧ CompV D B 2 L16 H3 H4 H6 M ∧
        CompV D B 3 L24 H4 H5 H6 M ∧ CompV D B 4 L32 H5 H6 H6 M) ∧ HeapIs G H6 ∧
      H3.toNat ≤ H4.toNat ∧ H4.toNat ≤ H5.toNat ∧ H5.toNat ≤ H6.toNat ∧ H6.toNat ≤ 33806089496 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G) _ _
      (fun s _ _ ⟨H4,L16,H5,L24,H6,L32,⟨⟨la,lad,ll⟩,fr6,c0',c8',c16',c24',cv0',cv1',cv2',cv3',cv4'⟩,rest⟩ =>
        ⟨H + 32#64,L32,
        by simp [EV,evalHOLExact,evalListHOLExact,lad,wordOpHOL,wordOp,valueIsWord,valueWord],
        by simp [EV,evalHOLExact,ll],hwHk 32 (by omega),H4,L16,H5,L24,H6,L32,⟨⟨la,lad⟩,fun x hx => ?_,?_,?_,?_,?_,
        by simp,compV_frame cv0' (fun x l u => ?_),compV_frame cv1' (fun x l u => ?_),
        compV_frame cv2' (fun x l u => ?_),compV_frame cv3' (fun x l u => ?_),compV_frame cv4' (fun x l u => ?_)⟩,
        rest⟩)) ?_
  · have : x ≠ H + 32#64 := fun e => by rw [e,eHk 32 (by omega)] at hx; omega
    simp only [if_neg this]; exact (fr6 x hx)
  · have : H + 0#64 ≠ H + 32#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 0 (by omega),eHk 32 (by omega)] at this; omega
    simp only [if_neg this]; exact c0'
  · have : H + 8#64 ≠ H + 32#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 8 (by omega),eHk 32 (by omega)] at this; omega
    simp only [if_neg this]; exact c8'
  · have : H + 16#64 ≠ H + 32#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 16 (by omega),eHk 32 (by omega)] at this; omega
    simp only [if_neg this]; exact c16'
  · have : H + 24#64 ≠ H + 32#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [eHk 24 (by omega),eHk 32 (by omega)] at this; omega
    simp only [if_neg this]; exact c24'
  · have : x ≠ H + 32#64 := fun e => by rw [e,eHk 32 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 32#64 := fun e => by rw [e,eHk 32 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 32#64 := fun e => by rw [e,eHk 32 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 32#64 := fun e => by rw [e,eHk 32 (by omega)] at l; omega
    simp only [if_neg this]
  · have : x ≠ H + 32#64 := fun e => by rw [e,eHk 32 (by omega)] at l; omega
    simp only [if_neg this]
  -- htab_set(bal_accounts, addr, ad); return ad
  refine aqgd_conseq (P := fun L M G => (fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H))) L ∧ (fun M G => ∃ H4 L16 H5 L24 H6 L32 : BitVec 64,
      ((∀ x, x.toNat < H.toNat → M x = M1 x) ∧ M (H + 0#64) = .word H1 ∧ M (H + 8#64) = .word T8 ∧
        M (H + 16#64) = .word L16 ∧ M (H + 24#64) = .word L24 ∧ M (H + 32#64) = .word L32 ∧
        CompV D B 0 H1 H1 H2 H6 M ∧ CompV D B 1 T8 H2 H3 H6 M ∧ CompV D B 2 L16 H3 H4 H6 M ∧
        CompV D B 3 L24 H4 H5 H6 M ∧ CompV D B 4 L32 H5 H6 H6 M) ∧ HeapIs G H6 ∧
      H3.toNat ≤ H4.toNat ∧ H4.toNat ≤ H5.toNat ∧ H5.toNat ≤ H6.toNat ∧ H6.toNat ≤ 33806089496 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G) M G)
    (aqgd_ghostR (fun M9 G9 ⟨H4,L16,H5,L24,H6,L32,⟨fr9,c0',c8',c16',c24',c32',cv0',cv1',cv2',cv3',cv4'⟩,hH6,h34,h45,h56,
      hb6,hn6,bg6⟩ => ?_))
    (fun L M G ⟨H4,L16,H5,L24,H6,L32,⟨⟨la,lad⟩,rest⟩,rest2⟩ => ⟨⟨la,lad⟩,H4,L16,H5,L24,H6,L32,rest,rest2⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  have rvba9 : TabRV D B BA lba Hl (insert H ADs) M9 :=
    tabRV_mono (tabRV_frame rvba (fun x hx => fr9 x (bw.2.2 .ba trivial x (phba x hx)))) (le_refl _)
      (fun t ht => Or.inr ht)
  have hwB : ¬ TabPhys BA lba w := fun h => hwR .ba trivial (phba w h)
  refine aqgd_seq (aqgd_call_htabSet_rv2 (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "ad") = some (.val (.word H)))
    (.var .global (ofString "bal_accounts")) (.var .local (ofString "addr")) (.var .local (ofString "ad"))
    BA A H Hl H6 Nj lba (insert H ADs) M9 G9 hwP hwB rvba9 hH6 hn6 (by omega) Dall (Or.inl klba) sdba
    (Set.mem_insert _ _) hK hKE ?_) ?_
  · intro F s _ _ hg ⟨la,lad⟩
    have gb : s.globals.lookup (ofString "bal_accounts") = some (.val (.word BA)) := by rw [hg]; exact bg6.1
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la,lad,gb]
  refine aqgd_return _ (fun s v H' _ hG ⟨⟨⟨la,lad⟩,Hp,hHp,le,hn',frs⟩,srv⟩ _ ev => ?_)
  simp [EV,evalHOLExact,lad] at ev
  subst ev
  unfold GIs at hG; subst hG
  exact ⟨H,rfl,balEnsure_final bw c1 (by omega) (by omega) h34 h45 h56 hb6 fr9 c0' c8' c16' c24' c32' cv0' cv1' cv2'
    cv3' cv4' klba sdba phba frs srv hn'⟩

#print axioms balEnsure_final
#print axioms balEnsure_aqgd
end be
end InitECandidate.Runtime
