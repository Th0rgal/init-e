import InitECandidate.Runtime.PtAdStorGD
/-!
The actual `add_storage_write(addr, slot, idx, new_value)`: ensure the account record, look the slot up in the
record's slot table `t0`; a missing slot gets a fresh storage-write list (`lst_new(40, 2)`) installed by `htab_set`;
then the transaction index is upserted into the slot's list and the value stored in the element. The
block-access-list state steps from the entry.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Locals of `add_storage_write`. -/
def SWL (A Sl I v0 v1 v2 v3 : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "slot") = some (.val (.word Sl)) ∧
  L.lookup (ofString "idx") = some (.val (.word I)) ∧
  L.lookup (ofString "new_value") = some (.rStruct [.val (.word v0),.val (.word v1),.val (.word v2),.val (.word v3)])

theorem swl_upd {A Sl I v0 v1 v2 v3 : BitVec 64} {L : GA} (h : SWL A Sl I v0 v1 v2 v3 L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "addr" ≠ x) (h2 : ofString "slot" ≠ x) (h3 : ofString "idx" ≠ x) (h4 : ofString "new_value" ≠ x) :
    SWL A Sl I v0 v1 v2 v3 (L.update (x,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.2.2.1,by rw [lookup_update_ne' _ _ h4]; exact h.2.2.2⟩

/-- The state after the slot lookup/installation of `add_storage_write`: local `l` names a storage-write list `lv`
owned in `R` (record region `O` or fresh heap), with a finisher rebuilding the record after the list changes. -/
def SWJ (D : BitVec 64 → Prop) (B : Bool) (BA IA IS KB Ix A Sl I v0 v1 v2 v3 ad : BitVec 64) (O : BitVec 64 → Prop)
    (H' Nj : BitVec 64) (M2 : Mem) (lv Hc : BitVec 64) (R : BitVec 64 → Prop) (M : Mem) (G : GA) : Prop :=
  HeapIs G Hc ∧ H'.toNat ≤ Hc.toNat ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
    BalG BA IA IS KB Ix G ∧ LstO 40#64 R lv M ∧ (∀ x, R x → O x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧
    (∀ x, x.toNat < H'.toNat → ¬ O x → M x = M2 x) ∧
    ∀ (M' : Mem) (Hf : BitVec 64), Hc.toNat ≤ Hf.toNat →
      LstO 40#64 (fun x => R x ∨ (Hc.toNat ≤ x.toNat ∧ x.toNat < Hf.toNat)) lv M' →
      (∀ x, x.toNat < Hc.toNat → ¬ R x → M' x = M x) →
      AdO D B (fun x => O x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hf.toNat)) ad Hf M'

section sw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The tail of `add_storage_write`: upsert the index into the slot's list, store the value, return 0. -/
theorem swTail_aqgd (bk : BalKeep) (BA IA IS KB Ix A Sl I v0 v1 v2 v3 ad : BitVec 64) (ADs ADs' : Set (BitVec 64))
    (Rg Rg' : BalK → BitVec 64 → Prop) (H H' Nj : BitVec 64) (M1 M2 : Mem)
    (bw' : BalW D B BA IA IS KB ADs' Rg' H' M2) (le : H.toNat ≤ H'.toNat) (sub : ADs ⊆ ADs')
    (gr : ∀ c, BalK.live ADs' c → ∀ x, Rg' c x → (BalK.live ADs c ∧ Rg c x) ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (fr : ∀ x, x.toNat < H.toNat → (∀ c, BalK.live ADs c → ¬ Rg c x) → M2 x = M1 x) (had : ad ∈ ADs')
    (hwO : ¬ Rg' (.ad ad) w) (hwH : w.toNat < H'.toNat) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ∃ (lv Hc : BitVec 64) (R : BitVec 64 → Prop),
        (SWL A Sl I v0 v1 v2 v3 L ∧ L.lookup (ofString "l") = some (.val (.word lv))) ∧
        SWJ D B BA IA IS KB Ix A Sl I v0 v1 v2 v3 ad (Rg' (.ad ad)) H' Nj M2 lv Hc R M G) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G)
      (.decCall (ofString "e") .one (ofString "lst_upsert_idx")
        [.var .local (ofString "l"),.const 40#64,.var .local (ofString "idx")]
        ((ProgHOL.store (.op .add [.var .local (ofString "e"),.const 8#64]) (.var .local (ofString "new_value"))).seq
          (.return (.const 0#64)))) := by
  have hbl := bw'.2.2 (.ad ad) had
  refine aqgd_ex (fun lv => aqgd_ex (fun Hc => aqgd_ex (fun R =>
    aqgd_ghostR (fun M3 G3 ⟨hH3,le3,hn3,bg3,lo,hR,fr3,fin⟩ => ?_))))
  have hO : ∀ x, R x → x.toNat < Hc.toNat := fun x hx => by
    rcases hR x hx with h | ⟨_,h⟩
    · have := hbl x h; omega
    · exact h
  have hwR : ¬ R w := fun h => by
    rcases hR w h with h | ⟨h,_⟩
    · exact hwO h
    · omega
  refine aqgd_of_arenaFact (Φ := Hc.toNat ≤ 33806089496 ∧ Hc.toNat % 8 = 0)
    (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact (jws_heap_facts aw.1.1.1 hH3).2) ?_
  intro ⟨hHE,hHal⟩
  refine aqgd_decCall_lstUpsert_b bk BA IA IS KB Ix
    (LP := fun L => SWL A Sl I v0 v1 v2 v3 L ∧ L.lookup (ofString "l") = some (.val (.word lv)))
    (Pc := fun L M G => ∃ S Hd : BitVec 64, ((SWL A Sl I v0 v1 v2 v3 L ∧
        L.lookup (ofString "e") = some (.val (.word S))) ∧
      LstO 40#64 (fun x => R x ∨ (Hc.toNat ≤ x.toNat ∧ x.toNat < Hd.toNat)) lv M ∧
      (∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + 40 →
        (R x ∨ (Hc.toNat ≤ x.toNat ∧ x.toNat < Hd.toNat)) ∧ ¬ HdW lv x) ∧
      (∀ x, x.toNat < Hc.toNat → ¬ R x → M x = M3 x)) ∧ HeapIs G Hd ∧ Hc.toNat ≤ Hd.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G)
    (Qc := fun _ _ _ => False) (ofString "e") _ _ _ lv 40#64 I R Hc Nj M3 G3 lo hH3 hn3 bg3 hO hwR (by omega) (by decide)
    hHal ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ ⟨⟨_,_,li,_⟩,ll⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,li,ll]
  · intro L S Hd M' G' ⟨lp,_⟩ hHd le' hn'' lo' el fr' bg'
    exact ⟨S,Hd,⟨⟨swl_upd lp _ _ (by decide) (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,lo',
      fun x l u => el x l (by simpa using u),fr'⟩,hHd,le',hn'',bg'⟩
  refine aqgd_ex (fun S => aqgd_ex (fun Hd => ?_))
  refine aqgd_of_arenaFact (Φ := Hd.toNat ≤ 33806089496)
    (fun _ _ g aw ⟨_,hH,_⟩ => (jws_heap_facts aw.1.1.1 hH).2.1) ?_
  intro hdE
  refine aqgd_seq (aqgd_storeV (Q := fun L M G => (SWL A Sl I v0 v1 v2 v3 L ∧
      LstO 40#64 (fun x => R x ∨ (Hc.toNat ≤ x.toNat ∧ x.toNat < Hd.toNat)) lv M ∧
      (∀ x, x.toNat < Hc.toNat → ¬ R x → M x = M3 x)) ∧ HeapIs G Hd ∧ Hc.toNat ≤ Hd.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj))) _ _
    (fun s _ _ ⟨⟨⟨lp,le_⟩,lo',el,fr'⟩,hHd,le',hn'',_⟩ => ?_)) ?_
  · have S0 := el S (le_refl _) (by omega)
    have Sb : S.toNat < Hd.toNat := by
      rcases S0.1 with h | ⟨_,h⟩
      · have := hO S h; omega
      · exact h
    have ew : ∀ j : Nat, j < 4 → (S + 8#64 + BitVec.ofNat 64 (8 * j)).toNat = S.toNat + 8 + 8 * j := fun j hj => by
      rw [BitVec.toNat_add,BitVec.toNat_add]; simp; omega
    refine ⟨S + 8#64,4,by simp [EV,evalHOLExact,evalListHOLExact,le_,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun x hx => ?_,fun j hj e => ?_,fun M' hM' => ⟨⟨lp,lstO_frame_hdr lo' (fun x hx => ?_),fun x hx hr => ?_⟩,
        hHd,le',hn''⟩⟩
    · simp [EV,evalHOLExact,lp.2.2.2] at hx
      subst hx; simp [flattenHOL]
    · have := el (S + 8#64 + BitVec.ofNat 64 (8 * j)) (by rw [ew j hj]; omega) (by rw [ew j hj]; omega)
      rw [← e] at this
      rcases this.1 with h | ⟨h,_⟩
      · exact hwR h
      · omega
    · refine hM' x (fun j hj e => ?_)
      have := el (S + 8#64 + BitVec.ofNat 64 (8 * j)) (by rw [ew j hj]; omega) (by rw [ew j hj]; omega)
      rw [← e] at this
      exact this.2 hx
    · refine (hM' x (fun j hj e => ?_)).trans (fr' x hx hr)
      have := el (S + 8#64 + BitVec.ofNat 64 (8 * j)) (by rw [ew j hj]; omega) (by rw [ew j hj]; omega)
      rw [← e] at this
      rcases this.1 with h | ⟨h,_⟩
      · exact hr h
      · omega
  refine aqgd_return _ (fun s v H'' _ hG ⟨⟨_,lo',fr'⟩,hHd,le',hn''⟩ _ ev => ?_)
  simp [EV,evalHOLExact] at ev
  subst ev
  refine ⟨rfl,balStep_upd bw' le sub gr fr (.ad ad) had (by omega) (fin s.memory Hd le' lo' fr')
    (fun x hx hr => ?_) hHd hn''⟩
  have nR : ¬ R x := fun h => by
    rcases hR x h with h | ⟨h,_⟩
    · exact hr h
    · omega
  exact (fr' x (by omega) nR).trans (fr3 x hx hr)

#print axioms swTail_aqgd

/-- The missing-slot branch of `add_storage_write`: `l = lst_new(40, 2); htab_set(t, slot, l)`. -/
theorem swNew_aqgd (bk : BalKeep) (BA IA IS KB Ix A Sl I v0 v1 v2 v3 ad : BitVec 64) {O : BitVec 64 → Prop}
    {Ls : Set (BitVec 64)} {RgA : AdC → BitVec 64 → Prop} {t0 t8 l16 l24 l32 : BitVec 64} {l0 : TLay}
    {Hl0 H' Nj : BitVec 64} {M2 : Mem} {G2 : GA}
    (cells : M2 ad = .word t0 ∧ M2 (ad + 8#64) = .word t8 ∧ M2 (ad + 16#64) = .word l16 ∧
      M2 (ad + 24#64) = .word l24 ∧ M2 (ad + 32#64) = .word l32) (hrw : ∀ x, RecW ad x → RgA .recw x)
    (rv : TabRV D B t0 l0 Hl0 Ls M2) (hl : Hl0.toNat ≤ H'.toNat) (kl : l0.KL = 32#64) (sd : l0.SD.toNat ≤ 56)
    (ph : ∀ x, TabPhys t0 l0 x → RgA .t0 x)
    (tO : TabO (RgA .t8) t8 H' M2) (a : LstO 40#64 (RgA .l16) l16 M2) (b : LstO 16#64 (RgA .l24) l24 M2)
    (c : LstO 24#64 (RgA .l32) l32 M2) (ls : ∀ l ∈ Ls, LstO 40#64 (RgA (.lst l)) l M2)
    (dis : RgDis (AdC.live Ls) RgA) (inO : ∀ c, AdC.live Ls c → ∀ x, RgA c x → O x)
    (hH2 : HeapIs G2 H') (hn2 : G2.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (bg2 : BalG BA IA IS KB Ix G2) (hO : ∀ x, O x → x.toNat < H'.toNat) (hwO : ¬ O w)
    (hwP : w.toNat < P0.toNat) (hwH : w.toNat < H'.toNat)
    (hS : Sl.toNat % 8 = 0) (hSE : Sl.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (SWL A Sl I v0 v1 v2 v3 L ∧ L.lookup (ofString "t") = some (.val (.word t0))) ∧
        M = M2 ∧ G = G2)
      (fun L M G => ∃ (lv Hc : BitVec 64) (R : BitVec 64 → Prop),
        (SWL A Sl I v0 v1 v2 v3 L ∧ L.lookup (ofString "l") = some (.val (.word lv))) ∧
        SWJ D B BA IA IS KB Ix A Sl I v0 v1 v2 v3 ad O H' Nj M2 lv Hc R M G) RR
      ((ProgHOL.call (some (some (.local,ofString "l"),none)) (ofString "lst_new") [.const 40#64,.const 2#64]).seq
        (.call (some (none,none)) (ofString "htab_set")
          [.var .local (ofString "t"),.var .local (ofString "slot"),.var .local (ofString "l")])) := by
  have pT : ∀ x, TabPhys t0 l0 x → x.toNat < H'.toNat := fun x hx => hO x (inO .t0 trivial x (ph x hx))
  refine aqgd_seq (Q := fun L M G => ∃ X H1 : BitVec 64, ((SWL A Sl I v0 v1 v2 v3 L ∧
      L.lookup (ofString "t") = some (.val (.word t0))) ∧ L.lookup (ofString "l") = some (.val (.word X))) ∧
      (LNew 40#64 2#64 H' M2 X H1 M G ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        BalG BA IA IS KB Ix G))
    (aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_callAssign_lstNew_g (LP := fun L => SWL A Sl I v0 v1 v2 v3 L ∧
        L.lookup (ofString "t") = some (.val (.word t0))) (ofString "l") 40#64 2#64 H' Nj M2 G2 hH2 hn2 hwH))
      (fun L M G h => ⟨h,by rw [h.2.2]; exact bg2⟩)
      (fun L M G ⟨⟨L0,X,H1,eL,⟨lp,lt⟩,ln,jn⟩,bg⟩ => by
        subst eL
        exact ⟨X,H1,⟨⟨swl_upd lp _ _ (by decide) (by decide) (by decide) (by decide),
          by rw [lookup_update_ne' _ _ (by decide)]; exact lt⟩,lookup_update_eq' _ _ _⟩,ln,jn,bg⟩)
      (fun _ _ _ h => h.1)) ?_
  refine aqgd_ex (fun X => aqgd_ex (fun H1 => aqgd_ghostR (fun M3 G3 ⟨ln,jn3,bg3⟩ => ?_)))
  have lo3 := lstO_of_lnew ln (by decide) (by decide)
  obtain ⟨hX,⟨Pp,hXP,_,hP⟩,hH3,hH1E,fr3⟩ := ln
  have e80 : (40#64 * 2#64 : BitVec 64).toNat = 80 := by decide
  rw [e80] at hP
  have rv3 : TabRV D B t0 l0 Hl0 (insert X Ls) M3 :=
    tabRV_mono (tabRV_frame rv (fun x hx => fr3 x (pT x hx))) (le_refl _) (fun _ h => Set.mem_insert_of_mem _ h)
  refine aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_call_htabSet_rv2 (LP := fun L => (SWL A Sl I v0 v1 v2 v3 L ∧
        L.lookup (ofString "t") = some (.val (.word t0))) ∧ L.lookup (ofString "l") = some (.val (.word X))) _ _ _
        t0 Sl X Hl0 H1 Nj l0 (insert X Ls) M3 G3 hwP (fun h => hwO (inO .t0 trivial w (ph w h))) rv3 hH3 jn3
        (by omega) Dall (Or.inr (Or.inl kl)) sd (Set.mem_insert _ _) hS hSE ?_))
    (fun L M G h => ⟨h,by rw [h.2.2]; exact bg3⟩) ?_ (fun _ _ _ h => h.1)
  · intro F s _ _ _ ⟨⟨lp,lt⟩,ll⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,lt,ll,lp.2.1]
  rintro L M G ⟨⟨⟨⟨⟨lp,_⟩,ll⟩,Hp,hHp,le1,jn,frs⟩,⟨lN,Hp2,hh2,_,rv4,klE,sdE,phl⟩⟩,bg⟩
  have eHp : Hp2 = Hp := by
    unfold HeapIs at hHp; rw [hHp] at hh2; simp only [Option.some.injEq,ValueHOL.val.injEq,
      HolWordLab.word.injEq] at hh2; exact hh2.symm
  subst eHp
  have hH'1 : H'.toNat ≤ H1.toNat := by omega
  have fr4 : ∀ x, x.toNat < H'.toNat → ¬ O x → M x = M2 x := fun x hx hn =>
    (frs x (fun h => hn (inO .t0 trivial x (ph x h))) (by omega)).trans (fr3 x hx)
  refine ⟨X,Hp2,fun x => H'.toNat ≤ x.toNat ∧ x.toNat < H1.toNat,⟨lp,ll⟩,hHp,by omega,jn,bg,
    lstO_frame lo3 (fun x ⟨x1,x2⟩ => frs x (fun h => by have := pT x h; omega) x2),
    fun x hx => Or.inr ⟨hx.1,by omega⟩,fr4,fun M' Hf le' lo' fr' => ?_⟩
  refine adO_stNew cells hrw tO a b c ls dis inO M' Hf X
    (fun x => RgA .t0 x ∨ (H1.toNat ≤ x.toNat ∧ x.toNat < Hp2.toNat))
    (fun x => (H'.toNat ≤ x.toNat ∧ x.toNat < H1.toNat) ∨ (Hp2.toNat ≤ x.toNat ∧ x.toNat < Hf.toNat)) lN Hp2
    (by omega) (tabRV_frame rv4 (fun x hx => fr' x ?_ ?_)) le' (by rw [klE]; exact kl) (by rw [sdE]; exact sd)
    (fun x hx => ?_) (fun x hx => ?_) lo' (fun x hx => ?_) (fun x hx hr => ?_) (fun x hx hn => ?_) hO
  · rcases phl x hx with h | ⟨_,h⟩
    · have := pT x h; omega
    · exact h
  · rintro ⟨h1,h2⟩
    rcases phl x hx with h | ⟨h,_⟩
    · have := pT x h; omega
    · omega
  · rcases phl x hx with h | h
    · exact Or.inl (ph x h)
    · exact Or.inr h
  · rcases hx with h | ⟨h1,h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega,by omega⟩
  · rcases hx with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1,by omega⟩
    · exact ⟨by omega,h2⟩
  · have := fun h => hO x (inO .t0 trivial x h)
    rcases hx with h | ⟨h1,h2⟩ <;> rcases hr with ⟨r1,r2⟩ | ⟨r1,r2⟩
    · have := this h; omega
    · have := this h; omega
    · omega
    · omega
  · refine (fr' x (by omega) (fun ⟨h1,_⟩ => by omega)).trans ((frs x (fun h => hn (ph x h)) (by omega)).trans
      (fr3 x hx))

#print axioms swNew_aqgd

theorem addStorage_aqgd (bk : BalKeep) (BA IA IS KB Ix A Sl I v0 v1 v2 v3 : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (hS : Sl.toNat % 8 = 0) (hSE : Sl.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => SWL A Sl I v0 v1 v2 v3 L ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G)
      (sourceFunctionBody Guest.guestFn_add_storage_write) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_add_storage_write,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  refine aqgd_decCall_balEnsure bk BA IA IS KB Ix A ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hwP p0 hK hKE Dall
    (LP := SWL A Sl I v0 v1 v2 v3)
    (Pc := fun L M G => ∃ ad : BitVec 64, (SWL A Sl I v0 v1 v2 v3 L ∧ L.lookup (ofString "ad") = some (.val (.word ad))) ∧
      (BalStepA D B BA IA IS KB ADs Rg H Nj M1 ad M G ∧ BalG BA IA IS KB Ix G))
    (Qc := fun _ _ _ => False) (ofString "ad") _ ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ lp
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,lp.1]
  · intro L ad M' G' lp st bg
    exact ⟨ad,⟨swl_upd lp _ _ (by decide) (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,st,bg⟩
  refine aqgd_ex (fun ad => aqgd_ghostR (fun M2 G2 ⟨⟨ADs',Rg',H',hH',le,hn',bw',sub,gr,fr,had⟩,bg⟩ => ?_))
  have adv : AdO D B (Rg' (.ad ad)) ad H' M2 := bw'.1 (.ad ad) had
  have hbl := bw'.2.2 (.ad ad) had
  have hwO : ¬ Rg' (.ad ad) w := fun h => by
    rcases gr (.ad ad) had w h with ⟨l1,h1⟩ | ⟨h1,_⟩
    · exact hwR _ l1 h1
    · omega
  have hwH : w.toNat < H'.toNat := by omega
  obtain ⟨t0,t8,l16,l24,l32,Ls,RgA,l0,Hl0,cells,hrw,⟨rv,hl,kl,sd,ph⟩,tO,a,b,c,ls,dis,inO⟩ := adv
  refine aqgd_of_arenaFact (Φ := H'.toNat ≤ 33806089496)
    (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact (jws_heap_facts aw.1.1.1 hH').2.1) ?_
  intro hHE
  have adD : ad.toNat < 33806089496 := by
    have := hbl _ (inO .recw trivial _ (hrw _ (Or.inl rfl))); omega
  have a0 : ad + 0#64 = ad := by simp
  refine aqgd_decD (Pb := fun L M G => (SWL A Sl I v0 v1 v2 v3 L ∧ L.lookup (ofString "t") = some (.val (.word t0))) ∧
      M = M2 ∧ G = G2)
    (Qb := fun _ _ _ => False) (ofString "t") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ dom _ ⟨⟨lp,la⟩,hM,hG⟩ _ ev _
    unfold EV at ev
    rw [eval_record_word s .local (ofString "ad") ad 0#64 t0 (by simp [evalHOLExact,la])
      (by rw [dom.2.1,a0]; exact Dall _ adD) (by rw [hM,a0]; exact cells.1)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨⟨swl_upd lp _ _ (by decide) (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,hM,hG⟩
  refine aqgd_decCall_htabGet_b bk BA IA IS KB Ix
    (LP := fun L => SWL A Sl I v0 v1 v2 v3 L ∧ L.lookup (ofString "t") = some (.val (.word t0)))
    (Pc := fun L M G => ((SWL A Sl I v0 v1 v2 v3 L ∧ L.lookup (ofString "t") = some (.val (.word t0))) ∧
      ∃ p val : BitVec 64, L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧
        (p ≠ 0 → val ∈ Ls)) ∧ M = M2 ∧ G = G2)
    (Qc := fun _ _ _ => False) (ofString "m") _ _ t0 Sl Hl0 H' l0 Ls M2 G2 rv hH' hl bg Dall (Or.inr (Or.inl kl)) hS hSE
    ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ ⟨lp,lt⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,lt,lp.2.1]
  · intro L p val ⟨lp,lt⟩ _ prop
    exact ⟨⟨⟨swl_upd lp _ _ (by decide) (by decide) (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact lt⟩,p,val,lookup_update_eq' _ _ _,prop⟩,rfl,rfl⟩
  refine aqgd_decD (Pb := fun L M G => ((SWL A Sl I v0 v1 v2 v3 L ∧ L.lookup (ofString "t") = some (.val (.word t0))) ∧
      ∃ p val : BitVec 64, L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧
        (p ≠ 0 → val ∈ Ls)) ∧ M = M2 ∧ G = G2)
    (Qb := fun _ _ _ => False) (ofString "l") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ _ _ ⟨⟨⟨lp,lt⟩,p,val,hm,prop⟩,hM,hG⟩ _ ev _
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨⟨⟨swl_upd lp _ _ (by decide) (by decide) (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact lt⟩,p,val,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hm,prop⟩,hM,hG⟩
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun L _ _ => ∃ p val : BitVec 64,
        L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ p ≠ 0)
      _ ?_ ?_ ?_) (swTail_aqgd bk BA IA IS KB Ix A Sl I v0 v1 v2 v3 ad ADs ADs' Rg Rg' H H' Nj M1 M2 bw' le sub gr fr had
        hwO hwH)
  · intro F s x H'' _ _ ⟨⟨_,p,val,hm,_⟩,_,_⟩ _ ev
    refine ⟨fun _ => trivial,fun hx => ⟨p,val,hm,fun hp => ?_⟩⟩
    subst hp hx
    simp [EV,evalHOLExact,hm,Compiler.Encoders.Asm.wordCmpHOL] at ev
  · exact aqgd_conseq (swNew_aqgd bk BA IA IS KB Ix A Sl I v0 v1 v2 v3 ad cells hrw rv hl kl sd ph tO a b c ls dis inO
      hH' hn' bg hbl hwO hwP hwH hS hSE Dall) (fun _ _ _ h => ⟨h.1.1.1,h.1.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  · refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨⟨lp,_⟩,p,val,hm,prop⟩,hM,hG⟩,⟨p',val',hm',hp'⟩⟩ _ ev => ?_)
    rw [hm] at hm'
    simp only [Option.some.injEq,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,
      HolWordLab.word.injEq,and_true] at hm'
    obtain ⟨rfl,rfl⟩ := hm'
    have hv := prop hp'
    simp [EV,evalHOLExact,hm] at ev; subst ev
    refine ⟨val,H',RgA (.lst val),⟨swl_upd lp _ _ (by decide) (by decide) (by decide) (by decide),
      lookup_update_eq' _ _ _⟩,by rw [hG]; exact hH',le_refl _,by rw [hG]; exact hn',by rw [hG]; exact bg,
      by rw [hM]; exact ls val hv,fun x h => Or.inl (inO (.lst val) hv x h),fun x _ _ => by rw [hM],
      fun M' Hf le' lo' fr' => adO_stOld cells hrw ⟨rv,hl,kl,sd,ph⟩ tO a b c ls dis inO val hv M' Hf le' lo'
        (fun x hx hr => by rw [fr' x hx hr,hM]) hbl⟩

#print axioms addStorage_aqgd

end sw
end InitECandidate.Runtime
