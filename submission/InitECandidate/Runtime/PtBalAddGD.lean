import InitECandidate.Runtime.PtBalEnsureGD
import InitECandidate.Runtime.PtStoreGD
/-!
The block-access-list change writers: a store of a value of known word count inside an element (`aqgd_storeV`), the
update of one change list of an account record (`adO_lst16`/`24`/`32`: the list kept with its region grown by fresh
heap, everything else of the record by frame).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section sv
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A store of a value of at most `k` words at `a`: only `a + 8j`, `j < k`, change. -/
theorem aqgd_storeV {P Q : GA → Mem → GA → Prop} (d v : ExpHOL 64)
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → DomD D B s → P s.locals s.memory s.globals →
      ∃ (a : BitVec 64) (k : Nat), EV s d = some (.val (.word a)) ∧
        (∀ x, EV s v = some x → (flattenHOL x).length ≤ k) ∧ (∀ j, j < k → w ≠ a + BitVec.ofNat 64 (8 * j)) ∧
        ∀ M' : Mem, (∀ y, (∀ j, j < k → y ≠ a + BitVec.ofNat 64 (8 * j)) → M' y = s.memory y) →
          Q s.locals M' s.globals) :
    AQGD D B A w Vn P Q RR (.store d v) := by
  intro F s code dom aw sl H hH pre
  unfold GIs at hH; subst hH
  obtain ⟨a,k,ha,hk,hw,hq⟩ := h s aw dom pre
  obtain ⟨loc,glob,res⟩ := evaluate_store_any s d v a ha
  rcases res with ⟨e,hm⟩ | ⟨e,x,hx,_,fr⟩
  · refine ⟨by rw [hm],fun c => ?_,fun e' => ?_,fun v' e' => ?_,by rw [e]; simp,by rw [e]; simp⟩
    · rcases c with c | c | c | ⟨_,c⟩ <;> rw [e] at c <;> cases c
    · rw [e] at e'; cases e'
    · rw [e] at e'; cases e'
  · have lk := hk x hx
    refine ⟨fr w (fun j hj => hw j (by omega)),fun _ => by rw [glob]; exact aw,
      fun _ => ⟨by rw [loc]; exact sl,_,by unfold GIs; rw [glob],?_⟩,
      (fun v' e' => by rw [e] at e'; cases e'),by rw [e]; simp,by rw [e]; simp⟩
    rw [loc]
    exact hq _ (fun y hy => fr y (fun j hj => hy j (by omega)))

#print axioms aqgd_storeV
end sv

section al
variable {D : BitVec 64 → Prop} {B : Bool}

/-- Update of the balance list (`ad + 16`, element size 40) of an account record. -/
theorem adO_lst16 {O : BitVec 64 → Prop} {ad H : BitVec 64} {M : Mem} (h : AdO D B O ad H M) :
    ∃ (l : BitVec 64) (R : BitVec 64 → Prop), M (ad + 16#64) = .word l ∧ LstO 40#64 R l M ∧ (∀ x, R x → O x) ∧
      ∀ (M' : Mem) (H' : BitVec 64), H.toNat ≤ H'.toNat →
        LstO 40#64 (fun x => R x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) l M' →
        (∀ x, x.toNat < H.toNat → ¬ R x → M' x = M x) → (∀ x, O x → x.toNat < H.toNat) →
        AdO D B (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ad H' M' := by
  obtain ⟨t0,t8,l16,l24,l32,Ls,Rg,l0,Hl0,⟨c0,c8,c16,c24,c32⟩,hrw,⟨rv,hl,kl,sd,ph⟩,tO,a,b,c,ls,dis,inO⟩ := h
  refine ⟨l16,Rg .l16,c16,a,inO .l16 trivial,fun M' H' le lo fr hO => ?_⟩
  have k : ∀ cc, AdC.live Ls cc → cc ≠ .l16 → ∀ x, Rg cc x → M' x = M x := fun cc hc ne x hx =>
    fr x (hO x (inO cc hc x hx)) (fun h => dis cc .l16 hc trivial ne x hx h)
  have kr : ∀ x, RecW ad x → M' x = M x := fun x hx => k .recw trivial (by decide) x (hrw x hx)
  refine ⟨t0,t8,l16,l24,l32,Ls,fun cc x => Rg cc x ∨ (cc = .l16 ∧ H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat),l0,Hl0,
    ⟨?_,?_,?_,?_,?_⟩,fun x hx => Or.inl (hrw x hx),
    ⟨tabRV_frame rv (fun x hx => k .t0 trivial (by decide) x (ph x hx)),by omega,kl,sd,fun x hx => Or.inl (ph x hx)⟩,
    tabO_sub (tabO_mono (tabO_frame tO (k .t8 trivial (by decide))) le) (fun x h => Or.inl h),
    lstO_sub lo (fun x h => by
      rcases h with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl,h1,h2⟩),
    lstO_sub (lstO_frame b (k .l24 trivial (by decide))) (fun x h => Or.inl h),
    lstO_sub (lstO_frame c (k .l32 trivial (by decide))) (fun x h => Or.inl h),
    fun l hl => lstO_sub (lstO_frame (ls l hl) (k (.lst l) hl (by simp))) (fun x h => Or.inl h),
    fun c1 c2 h1 h2 ne x hx1 hx2 => ?_,fun cc hc x hx => ?_⟩
  · rw [kr _ (Or.inl rfl)]; exact c0
  · rw [kr _ (Or.inr (Or.inl rfl))]; exact c8
  · rw [kr _ (Or.inr (Or.inr (Or.inl rfl)))]; exact c16
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact c24
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact c32
  · rcases hx1 with g1 | ⟨e1,a1,_⟩ <;> rcases hx2 with g2 | ⟨e2,a2,_⟩
    · exact dis c1 c2 h1 h2 ne x g1 g2
    · have := hO x (inO c1 h1 x g1); omega
    · have := hO x (inO c2 h2 x g2); omega
    · exact ne (e1.trans e2.symm)
  · rcases hx with g | ⟨_,a1,b1⟩
    · exact Or.inl (inO cc hc x g)
    · exact Or.inr ⟨a1,b1⟩

#print axioms adO_lst16

/-- Update of the nonce list (`ad + 24`, element size 16) of an account record. -/
theorem adO_lst24 {O : BitVec 64 → Prop} {ad H : BitVec 64} {M : Mem} (h : AdO D B O ad H M) :
    ∃ (l : BitVec 64) (R : BitVec 64 → Prop), M (ad + 24#64) = .word l ∧ LstO 16#64 R l M ∧ (∀ x, R x → O x) ∧
      ∀ (M' : Mem) (H' : BitVec 64), H.toNat ≤ H'.toNat →
        LstO 16#64 (fun x => R x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) l M' →
        (∀ x, x.toNat < H.toNat → ¬ R x → M' x = M x) → (∀ x, O x → x.toNat < H.toNat) →
        AdO D B (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ad H' M' := by
  obtain ⟨t0,t8,l16,l24,l32,Ls,Rg,l0,Hl0,⟨c0,c8,c16,c24,c32⟩,hrw,⟨rv,hl,kl,sd,ph⟩,tO,a,b,c,ls,dis,inO⟩ := h
  refine ⟨l24,Rg .l24,c24,b,inO .l24 trivial,fun M' H' le lo fr hO => ?_⟩
  have k : ∀ cc, AdC.live Ls cc → cc ≠ .l24 → ∀ x, Rg cc x → M' x = M x := fun cc hc ne x hx =>
    fr x (hO x (inO cc hc x hx)) (fun h => dis cc .l24 hc trivial ne x hx h)
  have kr : ∀ x, RecW ad x → M' x = M x := fun x hx => k .recw trivial (by decide) x (hrw x hx)
  refine ⟨t0,t8,l16,l24,l32,Ls,fun cc x => Rg cc x ∨ (cc = .l24 ∧ H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat),l0,Hl0,
    ⟨?_,?_,?_,?_,?_⟩,fun x hx => Or.inl (hrw x hx),
    ⟨tabRV_frame rv (fun x hx => k .t0 trivial (by decide) x (ph x hx)),by omega,kl,sd,fun x hx => Or.inl (ph x hx)⟩,
    tabO_sub (tabO_mono (tabO_frame tO (k .t8 trivial (by decide))) le) (fun x h => Or.inl h),
    lstO_sub (lstO_frame a (k .l16 trivial (by decide))) (fun x h => Or.inl h),
    lstO_sub lo (fun x h => by
      rcases h with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl,h1,h2⟩),
    lstO_sub (lstO_frame c (k .l32 trivial (by decide))) (fun x h => Or.inl h),
    fun l hl => lstO_sub (lstO_frame (ls l hl) (k (.lst l) hl (by simp))) (fun x h => Or.inl h),
    fun c1 c2 h1 h2 ne x hx1 hx2 => ?_,fun cc hc x hx => ?_⟩
  · rw [kr _ (Or.inl rfl)]; exact c0
  · rw [kr _ (Or.inr (Or.inl rfl))]; exact c8
  · rw [kr _ (Or.inr (Or.inr (Or.inl rfl)))]; exact c16
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact c24
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact c32
  · rcases hx1 with g1 | ⟨e1,a1,_⟩ <;> rcases hx2 with g2 | ⟨e2,a2,_⟩
    · exact dis c1 c2 h1 h2 ne x g1 g2
    · have := hO x (inO c1 h1 x g1); omega
    · have := hO x (inO c2 h2 x g2); omega
    · exact ne (e1.trans e2.symm)
  · rcases hx with g | ⟨_,a1,b1⟩
    · exact Or.inl (inO cc hc x g)
    · exact Or.inr ⟨a1,b1⟩

#print axioms adO_lst24

/-- Update of the code list (`ad + 32`, element size 24) of an account record. -/
theorem adO_lst32 {O : BitVec 64 → Prop} {ad H : BitVec 64} {M : Mem} (h : AdO D B O ad H M) :
    ∃ (l : BitVec 64) (R : BitVec 64 → Prop), M (ad + 32#64) = .word l ∧ LstO 24#64 R l M ∧ (∀ x, R x → O x) ∧
      ∀ (M' : Mem) (H' : BitVec 64), H.toNat ≤ H'.toNat →
        LstO 24#64 (fun x => R x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) l M' →
        (∀ x, x.toNat < H.toNat → ¬ R x → M' x = M x) → (∀ x, O x → x.toNat < H.toNat) →
        AdO D B (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ad H' M' := by
  obtain ⟨t0,t8,l16,l24,l32,Ls,Rg,l0,Hl0,⟨c0,c8,c16,c24,c32⟩,hrw,⟨rv,hl,kl,sd,ph⟩,tO,a,b,c,ls,dis,inO⟩ := h
  refine ⟨l32,Rg .l32,c32,c,inO .l32 trivial,fun M' H' le lo fr hO => ?_⟩
  have k : ∀ cc, AdC.live Ls cc → cc ≠ .l32 → ∀ x, Rg cc x → M' x = M x := fun cc hc ne x hx =>
    fr x (hO x (inO cc hc x hx)) (fun h => dis cc .l32 hc trivial ne x hx h)
  have kr : ∀ x, RecW ad x → M' x = M x := fun x hx => k .recw trivial (by decide) x (hrw x hx)
  refine ⟨t0,t8,l16,l24,l32,Ls,fun cc x => Rg cc x ∨ (cc = .l32 ∧ H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat),l0,Hl0,
    ⟨?_,?_,?_,?_,?_⟩,fun x hx => Or.inl (hrw x hx),
    ⟨tabRV_frame rv (fun x hx => k .t0 trivial (by decide) x (ph x hx)),by omega,kl,sd,fun x hx => Or.inl (ph x hx)⟩,
    tabO_sub (tabO_mono (tabO_frame tO (k .t8 trivial (by decide))) le) (fun x h => Or.inl h),
    lstO_sub (lstO_frame a (k .l16 trivial (by decide))) (fun x h => Or.inl h),
    lstO_sub (lstO_frame b (k .l24 trivial (by decide))) (fun x h => Or.inl h),
    lstO_sub lo (fun x h => by
      rcases h with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl,h1,h2⟩),
    fun l hl => lstO_sub (lstO_frame (ls l hl) (k (.lst l) hl (by simp))) (fun x h => Or.inl h),
    fun c1 c2 h1 h2 ne x hx1 hx2 => ?_,fun cc hc x hx => ?_⟩
  · rw [kr _ (Or.inl rfl)]; exact c0
  · rw [kr _ (Or.inr (Or.inl rfl))]; exact c8
  · rw [kr _ (Or.inr (Or.inr (Or.inl rfl)))]; exact c16
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact c24
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact c32
  · rcases hx1 with g1 | ⟨e1,a1,_⟩ <;> rcases hx2 with g2 | ⟨e2,a2,_⟩
    · exact dis c1 c2 h1 h2 ne x g1 g2
    · have := hO x (inO c1 h1 x g1); omega
    · have := hO x (inO c2 h2 x g2); omega
    · exact ne (e1.trans e2.symm)
  · rcases hx with g | ⟨_,a1,b1⟩
    · exact Or.inl (inO cc hc x g)
    · exact Or.inr ⟨a1,b1⟩

#print axioms adO_lst32

end al
section cmp
variable {D : BitVec 64 → Prop} {B : Bool} {BA IA IS KB : BitVec 64}

/-- After an ensure step (`BalW` at `ADs'`, `Rg'`, `H'`), an update of the live component `c` confined to its region
and `[H', Hc)` gives a step from the original entry. -/
theorem balStep_upd {ADs ADs' : Set (BitVec 64)} {Rg Rg' : BalK → BitVec 64 → Prop} {H H' Hc Nj : BitVec 64}
    {M1 M2 M3 : Mem} {G3 : GA} (bw' : BalW D B BA IA IS KB ADs' Rg' H' M2) (le : H.toNat ≤ H'.toNat)
    (sub : ADs ⊆ ADs')
    (gr : ∀ c, BalK.live ADs' c → ∀ x, Rg' c x → (BalK.live ADs c ∧ Rg c x) ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (fr : ∀ x, x.toNat < H.toNat → (∀ c, BalK.live ADs c → ¬ Rg c x) → M2 x = M1 x)
    (c : BalK) (hc : BalK.live ADs' c) (le' : H'.toNat ≤ Hc.toNat)
    (new : BalV D B BA IA IS KB ADs' c (fun x => Rg' c x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) Hc M3)
    (fr3 : ∀ x, x.toNat < H'.toNat → ¬ Rg' c x → M3 x = M2 x) (hH : HeapIs G3 Hc)
    (hn : G3.lookup (ofString "journal_n") = some (.val (.word Nj))) :
    BalStep D B BA IA IS KB ADs Rg H Nj M1 M3 G3 := by
  have bw3 := balW_upd c hc bw' le' new fr3
  refine ⟨ADs',_,Hc,hH,by omega,hn,bw3,sub,fun c' hc' x hx => ?_,fun x hx hn' => ?_⟩
  · rcases hx with h | ⟨_,h1,h2⟩
    · rcases gr c' hc' x h with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1,by omega⟩
    · exact Or.inr ⟨by omega,h2⟩
  · refine (fr3 x (by omega) (fun h => ?_)).trans (fr x hx hn')
    rcases gr c hc x h with ⟨l,h⟩ | ⟨h,_⟩
    · exact hn' c l h
    · omega

#print axioms balStep_upd
end cmp

section ce
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `var 1 name = bal_ensure_account(ea)`. -/
theorem aqgd_decCall_balEnsure (bk : BalKeep) (BA IA IS KB Ix A : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (ea : ExpHOL 64) {cont : ProgHOL 64}
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea] =
        some [.val (.word A)])
    (hres : ∀ (L : GA) (ad : BitVec 64) (M' : Mem) (G' : GA), LP L →
      BalStepA D B BA IA IS KB ADs Rg H Nj M1 ad M' G' → BalG BA IA IS KB Ix G' →
      Pc (L.update (name,.val (.word ad))) M' G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "bal_ensure_account") [ea] cont) := by
  refine aqgd_conseq (P := fun L M G => (LP L ∧ M = M1 ∧ G = G1) ∧ BalG BA IA IS KB Ix G) ?_
    (fun L M G h => ⟨h,by rw [h.2.2]; exact hB1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decCallSpecDB bk BA IA IS KB Ix (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "addr") = some (.val (.word A)) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ ad : BitVec 64, v = .val (.word ad) ∧ BalStepA D B BA IA IS KB ADs Rg H Nj M1 ad M' G')
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_balEnsureAccount_lookup
    (by simp [goodBal,balExtra]) (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
    (fun L M G L' M' G' ⟨lp,_,_⟩ qc => hq L L' M' G' lp qc)
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    exact aqgd_conseq (balEnsure_aqgd bk BA IA IS KB Ix A ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hwP p0 hK hKE Dall)
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)
  · intro F s values callee rs _ dom H' hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_balEnsureAccount_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,_,_⟩ bg ⟨ad,ev,st⟩ _
    subst ev
    exact hres L ad M' G' lp st bg

#print axioms aqgd_decCall_balEnsure
end ce
end InitECandidate.Runtime
