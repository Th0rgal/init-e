import InitECandidate.Runtime.PtBalChgGD
/-!
The actual `add_nonce_change(addr, idx, new_nonce)`: ensure the account record, scan its nonce list (element size 16)
for the transaction index (raising the stored nonce in place and returning when found), else push a new element holding
the index and the nonce; the block-access-list state steps from the entry.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Locals of `add_nonce_change`. -/
def ANL (A I Nn : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "idx") = some (.val (.word I)) ∧
  L.lookup (ofString "new_nonce") = some (.val (.word Nn))

theorem anl_upd {A I Nn : BitVec 64} {L : GA} (h : ANL A I Nn L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "addr" ≠ x) (h2 : ofString "idx" ≠ x) (h3 : ofString "new_nonce" ≠ x) :
    ANL A I Nn (L.update (x,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.2.2⟩

theorem anl_res {A I Nn : BitVec 64} {L : GA} (h : ANL A I Nn L) (x : MlS) (o : Option (ValueHOL 64))
    (h1 : ofString "addr" ≠ x) (h2 : ofString "idx" ≠ x) (h3 : ofString "new_nonce" ≠ x) :
    ANL A I Nn (L.resVarEq (x,o)) :=
  ⟨by rw [resVar_lookup_ne _ _ _ _ h1]; exact h.1,by rw [resVar_lookup_ne _ _ _ _ h2]; exact h.2.1,
    by rw [resVar_lookup_ne _ _ _ _ h3]; exact h.2.2⟩

theorem ev_pim {F : Type} (s : PanSemStateFiniteExact 64 F) (p i : MlS) (P Iv k e : BitVec 64)
    (hp : s.locals.lookup p = some (.val (.word P))) (hi : s.locals.lookup i = some (.val (.word Iv))) :
    EV s (.op .add [.var .local p,.panop .mul [.var .local i,.const k],.const e]) =
      some (.val (.word (P + Iv * k + e))) := by
  simp [EV,evalHOLExact,evalListHOLExact,hp,hi,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  exact (BitVec.add_assoc _ _ _).symm

section an
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

theorem addNonce_aqgd (bk : BalKeep) (BA IA IS KB Ix A I Nn : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ANL A I Nn L ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G)
      (sourceFunctionBody Guest.guestFn_add_nonce_change) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_add_nonce_change,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  refine aqgd_decCall_balEnsure bk BA IA IS KB Ix A ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hwP p0 hK hKE Dall
    (LP := ANL A I Nn)
    (Pc := fun L M G => ∃ ad : BitVec 64, (ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad))) ∧
      (BalStepA D B BA IA IS KB ADs Rg H Nj M1 ad M G ∧ BalG BA IA IS KB Ix G))
    (Qc := fun _ _ _ => False) (ofString "ad") _ ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ ⟨la,_,_⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la]
  · intro L ad M' G' lp st bg
    exact ⟨ad,⟨anl_upd lp _ _ (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,st,bg⟩
  refine aqgd_ex (fun ad => aqgd_ghostR (fun M2 G2 ⟨⟨ADs',Rg',H',hH',le,hn',bw',sub,gr,fr,had⟩,bg⟩ => ?_))
  have adv : AdO D B (Rg' (.ad ad)) ad H' M2 := bw'.1 (.ad ad) had
  have hbl := bw'.2.2 (.ad ad) had
  obtain ⟨l,R,cell,lo,hR,upd⟩ := adO_lst24 adv
  have hwO : ¬ R w := fun h => by
    rcases gr (.ad ad) had w (hR w h) with ⟨l1,h1⟩ | ⟨h1,_⟩
    · exact hwR _ l1 h1
    · omega
  have hO : ∀ x, R x → x.toNat < H'.toNat := fun x hx => hbl x (hR x hx)
  refine aqgd_of_arenaFact (Φ := H'.toNat ≤ 33806089496)
    (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact (jws_heap_facts aw.1.1.1 hH').2.1) ?_
  intro hHE
  have c24D : (ad + 24#64).toNat < 33806089496 := by
    obtain ⟨_,_,_,_,_,_,RgA,_,_,_,hrw,_,_,_,_,_,_,_,inO⟩ := adv
    have := hbl _ (inO .recw trivial _ (hrw _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))); omega
  have lo' := lo
  obtain ⟨P,N,Cp,⟨hd0,hd8,hd16⟩,hNC,hC0,al,hHd,hBuf⟩ := lo'
  have hl8 : (l + 8#64).toNat < 33806089496 := by have := hO _ (hHd _ (Or.inr (Or.inl rfl))); omega
  have hl0 : l.toNat < 33806089496 := by have := hO _ (hHd _ (Or.inl rfl)); omega
  have a0 : l + 0#64 = l := by simp
  -- var l = lds(ad + 24); var n = lds(l + 8); var p = lds(l + 0); var i = 0
  refine aqgd_decD (Pb := fun L M G => (ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧
      L.lookup (ofString "l") = some (.val (.word l))) ∧ M = M2 ∧ G = G2) (Qb := fun _ _ _ => False)
    (ofString "l") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ dom _ ⟨⟨lp,lad⟩,hM,hG2⟩ _ ev _
    unfold EV at ev
    rw [eval_record_word s .local (ofString "ad") ad 24#64 l (by simp [evalHOLExact,lad])
      (by rw [dom.2.1]; exact Dall _ c24D) (by rw [hM]; exact cell)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨⟨anl_upd lp _ _ (by decide) (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact lad,
      lookup_update_eq' _ _ _⟩,hM,hG2⟩
  refine aqgd_decD (Pb := fun L M G => (ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧
      L.lookup (ofString "l") = some (.val (.word l)) ∧ L.lookup (ofString "n") = some (.val (.word N))) ∧ M = M2 ∧
      G = G2) (Qb := fun _ _ _ => False)
    (ofString "n") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ dom _ ⟨⟨lp,lad,ll⟩,hM,hG2⟩ _ ev _
    unfold EV at ev
    rw [eval_record_word s .local (ofString "l") l 8#64 N (by simp [evalHOLExact,ll])
      (by rw [dom.2.1]; exact Dall _ hl8) (by rw [hM]; exact hd8)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨⟨anl_upd lp _ _ (by decide) (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact lad,
      by rw [lookup_update_ne' _ _ (by decide)]; exact ll,lookup_update_eq' _ _ _⟩,hM,hG2⟩
  refine aqgd_decD (Pb := fun L M G => (ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧
      L.lookup (ofString "l") = some (.val (.word l)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
      L.lookup (ofString "p") = some (.val (.word P))) ∧ M = M2 ∧ G = G2) (Qb := fun _ _ _ => False)
    (ofString "p") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ dom _ ⟨⟨lp,lad,ll,ln⟩,hM,hG2⟩ _ ev _
    unfold EV at ev
    rw [eval_record_word s .local (ofString "l") l 0#64 P (by simp [evalHOLExact,ll])
      (by rw [dom.2.1,a0]; exact Dall _ hl0) (by rw [hM,a0]; exact hd0)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨⟨anl_upd lp _ _ (by decide) (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact lad,
      by rw [lookup_update_ne' _ _ (by decide)]; exact ll,by rw [lookup_update_ne' _ _ (by decide)]; exact ln,
      lookup_update_eq' _ _ _⟩,hM,hG2⟩
  refine aqgd_decD (Pb := fun L M G => ((ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧
      L.lookup (ofString "l") = some (.val (.word l)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
      L.lookup (ofString "p") = some (.val (.word P))) ∧ ∃ Iv : BitVec 64,
        L.lookup (ofString "i") = some (.val (.word Iv)) ∧ Iv.toNat ≤ N.toNat) ∧ M = M2 ∧ G = G2)
    (Qb := fun _ _ _ => False)
    (ofString "i") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ dom _ ⟨⟨lp,lad,ll,ln,lpp⟩,hM,hG2⟩ _ ev _
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨⟨⟨anl_upd lp _ _ (by decide) (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact lad,
      by rw [lookup_update_ne' _ _ (by decide)]; exact ll,by rw [lookup_update_ne' _ _ (by decide)]; exact ln,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lpp⟩,0#64,lookup_update_eq' _ _ _,by simp⟩,hM,hG2⟩
  have hbufle : P.toNat + 16 * Cp.toNat ≤ H'.toNat :=
    buf_le P.isLt H'.isLt (by have : (16#64).toNat = 16 := rfl; omega) (fun x l u => hO x (hBuf x l u).1)
  refine aqgd_seq (Q := fun L M G => (ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧ L.lookup (ofString "l") = some (.val (.word l)) ∧
        L.lookup (ofString "n") = some (.val (.word N)) ∧ L.lookup (ofString "p") = some (.val (.word P))) ∧ M = M2 ∧ G = G2) ?_ ?_
  · refine aqgd_conseq (aqgd_whileE (C := fun L _ _ => ∃ Iv : BitVec 64,
        L.lookup (ofString "i") = some (.val (.word Iv)) ∧ Iv.toNat < N.toNat) (E := fun _ _ _ => True)
        (Qb := fun _ _ _ => False) _ ?_ (fun _ _ _ _ _ _ _ _ => trivial) (aqgb_of_aqgd ?_))
      (fun _ _ _ h => h) (fun L M G h => h.elim (fun ⟨⟨⟨loc,_⟩,hM,hG⟩,_⟩ => ⟨loc,hM,hG⟩) False.elim)
      (fun _ _ _ h => h)
    · intro F s x _ _ ⟨⟨⟨_,_,_,ln,_⟩,Iv,hi,hle⟩,_,_⟩ _ ev hx
      simp [EV,evalHOLExact,hi,ln,slt_small (b := N) (show Iv.toNat < 2 ^ 63 by omega)] at ev
      split at ev
      · rename_i h; exact ⟨Iv,hi,h.2⟩
      · exact absurd ev.symm hx
    refine aqgd_conseq (P := fun L M G => ∃ Iv : BitVec 64, ((ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧ L.lookup (ofString "l") = some (.val (.word l)) ∧
        L.lookup (ofString "n") = some (.val (.word N)) ∧ L.lookup (ofString "p") = some (.val (.word P))) ∧ L.lookup (ofString "i") = some (.val (.word Iv)) ∧
        Iv.toNat < N.toNat) ∧ M = M2 ∧ G = G2) (aqgd_ex (fun Iv => ?_))
      (fun L M G ⟨⟨⟨loc,_⟩,hM,hG⟩,Iv,hi,hlt⟩ => ⟨Iv,⟨loc,hi,hlt⟩,hM,hG⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_seq (Q := fun L M G => ((ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧ L.lookup (ofString "l") = some (.val (.word l)) ∧
        L.lookup (ofString "n") = some (.val (.word N)) ∧ L.lookup (ofString "p") = some (.val (.word P))) ∧ L.lookup (ofString "i") = some (.val (.word Iv)) ∧
        Iv.toNat < N.toNat) ∧ M = M2 ∧ G = G2)
      (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
        (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
        (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
    · refine aqgd_conseq (P := fun L M G => ((((ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧ L.lookup (ofString "l") = some (.val (.word l)) ∧
        L.lookup (ofString "n") = some (.val (.word N)) ∧ L.lookup (ofString "p") = some (.val (.word P))) ∧ L.lookup (ofString "i") = some (.val (.word Iv)) ∧
          Iv.toNat < N.toNat) ∧ M = M2 ∧ G = G2) ∧ True) ∧ Iv.toNat < N.toNat) (aqgd_pureE (fun hlt => ?_))
        (fun L M G h => ⟨h,h.1.1.2.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
      have ea : (P + Iv * 16#64 + 8#64).toNat = P.toNat + Iv.toNat * 16 + 8 := by
        have : Iv.toNat * 16 < 2 ^ 64 := by omega
        rw [BitVec.toNat_add,BitVec.toNat_add,BitVec.toNat_mul]; simp; omega
      have ainB := hBuf (P + Iv * 16#64 + 8#64) (by rw [ea]; omega)
        (by rw [ea,show (16#64).toNat = 16 from rfl]; omega)
      refine aqgd_seq (Q := fun L M G => (((ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧ L.lookup (ofString "l") = some (.val (.word l)) ∧
        L.lookup (ofString "n") = some (.val (.word N)) ∧ L.lookup (ofString "p") = some (.val (.word P))) ∧ L.lookup (ofString "i") = some (.val (.word Iv)) ∧
          Iv.toNat < N.toNat) ∧ (∀ x, x ≠ P + Iv * 16#64 + 8#64 → M x = M2 x)) ∧ G = G2)
        (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
          (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
          (aqgd_storeW _ _ (fun s _ _ ⟨⟨⟨⟨⟨lp,lad,ll,ln,lpp⟩,hi,hlt⟩,hM,hG⟩,_⟩,_⟩ => ⟨P + Iv * 16#64 + 8#64,Nn,
            ev_pim s _ _ P Iv 16#64 8#64 lpp hi,by simp [EV,evalHOLExact,lp.2.2],fun e => hwO (e ▸ ainB.1),
            ⟨⟨⟨lp,lad,ll,ln,lpp⟩,hi,hlt⟩,fun x hx => by simp only [if_neg hx]; rw [hM]⟩,hG⟩))
          (aqgd_conseq aqgd_skip (fun _ _ _ h => ⟨⟨h.1.1.1,fun x _ => by rw [h.1.1.2.1]⟩,h.1.1.2.2⟩)
            (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
      refine aqgd_return _ (fun s v H'' _ hG ⟨⟨_,keep⟩,hG2⟩ _ ev => ?_)
      simp [EV,evalHOLExact] at ev
      subst ev
      have kh : ∀ x, HdW l x → s.memory x = M2 x := fun x hx => keep x (fun e => ainB.2 (e ▸ hx))
      have kf : ∀ x, x.toNat < H'.toNat → ¬ R x → s.memory x = M2 x := fun x _ hr =>
        keep x (fun e => hr (e ▸ ainB.1))
      unfold GIs at hG
      refine ⟨rfl,balStep_upd bw' le sub gr fr (.ad ad) had (le_refl _)
        (upd s.memory H' (le_refl _) (lstO_sub (lstO_frame_hdr lo kh) (fun x h => Or.inl h)) kf hbl)
        (fun x hx hr => kf x hx (fun h => hr (hR x h))) ?_ ?_⟩
      · rw [hG2]; exact hH'
      · rw [hG2]; exact hn'
    · refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨lp,lad,ll,ln,lpp⟩,hi,hlt⟩,hM,hG⟩ _ ev => ?_)
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      have e1 : (Iv + 1#64).toNat = Iv.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      exact ⟨⟨⟨anl_upd lp _ _ (by decide) (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact lad,
        by rw [lookup_update_ne' _ _ (by decide)]; exact ll,by rw [lookup_update_ne' _ _ (by decide)]; exact ln,
        by rw [lookup_update_ne' _ _ (by decide)]; exact lpp⟩,Iv + 1#64,lookup_update_eq' _ _ _,by rw [e1]; omega⟩,
        hM,hG⟩
  refine aqgd_decCall_lstPush_b bk BA IA IS KB Ix (LP := fun L => ANL A I Nn L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧ L.lookup (ofString "l") = some (.val (.word l)) ∧
        L.lookup (ofString "n") = some (.val (.word N)) ∧ L.lookup (ofString "p") = some (.val (.word P)))
    (Pc := fun L M G => ∃ S Hc : BitVec 64, ((ANL A I Nn L ∧ L.lookup (ofString "e") = some (.val (.word S))) ∧
      LstO 16#64 (fun x => R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) l M ∧
      (∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + 16 →
        (R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW l x) ∧
      (∀ x, x.toNat < H'.toNat → ¬ R x → M x = M2 x)) ∧ HeapIs G Hc ∧ H'.toNat ≤ Hc.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Qc := fun _ _ _ => False) (ofString "e") _ _ l 16#64 R H' Nj M2 G2 lo hH' hn' bg hO hwO (by omega) (by decide)
    ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ ⟨_,_,ll,_,_⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,ll]
  · intro L S Hc M' G' ⟨lp,_⟩ hHc le' hn'' lo' el fr' _
    exact ⟨S,Hc,⟨⟨anl_upd lp _ _ (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,lo',
      fun x l u => el x l (by simpa using u),fr'⟩,hHc,le',hn''⟩
  refine aqgd_ex (fun S => aqgd_ex (fun Hc => ?_))
  refine aqgd_of_arenaFact (Φ := Hc.toNat ≤ 33806089496)
    (fun _ _ g aw ⟨_,hH,_⟩ => (jws_heap_facts aw.1.1.1 hH).2.1) ?_
  intro hcE
  refine aqgd_seq (aqgd_storeW (Q := fun L M G => ((ANL A I Nn L ∧ L.lookup (ofString "e") = some (.val (.word S))) ∧
      LstO 16#64 (fun x => R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) l M ∧
      (∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + 16 →
        (R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW l x) ∧
      (∀ x, x.toNat < H'.toNat → ¬ R x → M x = M2 x)) ∧ HeapIs G Hc ∧ H'.toNat ≤ Hc.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj))) _ _
    (fun s _ _ ⟨⟨⟨lp,le_⟩,lo',el,fr'⟩,hHc,le',hn''⟩ => ?_)) ?_
  · have W := el S (le_refl _) (by omega)
    refine ⟨S,I,by simp [EV,evalHOLExact,le_],by simp [EV,evalHOLExact,lp.2.1],fun e => ?_,
      ⟨⟨lp,le_⟩,lstO_frame_hdr lo' (fun x hx => ?_),el,fun x hx hr => ?_⟩,hHc,le',hn''⟩
    · rw [← e] at W
      rcases W.1 with h | ⟨h,_⟩
      · exact hwO h
      · omega
    · have : x ≠ S := fun e => W.2 (e ▸ hx)
      simp only [if_neg this]
    · have : x ≠ S := fun e => by
        rw [e] at hx hr
        rcases W.1 with h | ⟨h,_⟩
        · exact hr h
        · omega
      simp only [if_neg this]; exact fr' x hx hr
  refine aqgd_seq (aqgd_storeW (Q := fun L M G => (ANL A I Nn L ∧
      LstO 16#64 (fun x => R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) l M ∧
      (∀ x, x.toNat < H'.toNat → ¬ R x → M x = M2 x)) ∧ HeapIs G Hc ∧ H'.toNat ≤ Hc.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj))) _ _
    (fun s _ _ ⟨⟨⟨lp,le_⟩,lo',el,fr'⟩,hHc,le',hn''⟩ => ?_)) ?_
  · have S0 := el S (le_refl _) (by omega)
    have Sb : S.toNat < Hc.toNat := by
      rcases S0.1 with h | ⟨_,h⟩
      · have := hO S h; omega
      · exact h
    have e8 : (S + 8#64).toNat = S.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    have W := el (S + 8#64) (by rw [e8]; omega) (by rw [e8]; omega)
    refine ⟨S + 8#64,Nn,by simp [EV,evalHOLExact,evalListHOLExact,le_,wordOpHOL,wordOp,valueIsWord,valueWord],
      by simp [EV,evalHOLExact,lp.2.2],fun e => ?_,⟨lp,lstO_frame_hdr lo' (fun x hx => ?_),
        fun x hx hr => ?_⟩,hHc,le',hn''⟩
    · rw [← e] at W
      rcases W.1 with h | ⟨h,_⟩
      · exact hwO h
      · omega
    · have : x ≠ S + 8#64 := fun e => W.2 (e ▸ hx)
      simp only [if_neg this]
    · have : x ≠ S + 8#64 := fun e => by
        rw [e] at hx hr
        rcases W.1 with h | ⟨h,_⟩
        · exact hr h
        · omega
      simp only [if_neg this]; exact fr' x hx hr
  refine aqgd_return _ (fun s v H'' _ hG ⟨⟨_,lo',fr'⟩,hHc,le',hn''⟩ _ ev => ?_)
  simp [EV,evalHOLExact] at ev
  subst ev
  exact ⟨rfl,balStep_upd bw' le sub gr fr (.ad ad) had le' (upd s.memory Hc le' lo' fr' hbl) (fun x hx hr => fr' x hx
    (fun h => hr (hR x h))) hHc hn''⟩

#print axioms addNonce_aqgd
end an
end InitECandidate.Runtime
