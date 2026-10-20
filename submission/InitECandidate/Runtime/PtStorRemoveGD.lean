import InitECandidate.Runtime.PtTabDelGD
/-!
The actual `remove_storage_write(addr, slot, idx)`: look the account up; look the slot up in its slot table; remove
the transaction index from the slot's list and, when the list becomes empty, delete the slot (`htab_del`). Everything
changes in place inside the record's table and list regions; the block-access-list state steps from the entry.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ad
variable {D : BitVec 64 → Prop} {B : Bool} {O : BitVec 64 → Prop} {ad H : BitVec 64} {M : Mem}

/-- The slot table and one storage-write list changed in place (same regions); the rest of the record by frame. -/
theorem adO_stDel {Ls : Set (BitVec 64)} {Rg : AdC → BitVec 64 → Prop} {t0 t8 l16 l24 l32 : BitVec 64}
    (cells : M ad = .word t0 ∧ M (ad + 8#64) = .word t8 ∧ M (ad + 16#64) = .word l16 ∧
      M (ad + 24#64) = .word l24 ∧ M (ad + 32#64) = .word l32) (hrw : ∀ x, RecW ad x → Rg .recw x)
    (tO : TabO (Rg .t8) t8 H M) (a : LstO 40#64 (Rg .l16) l16 M) (b : LstO 16#64 (Rg .l24) l24 M)
    (c : LstO 24#64 (Rg .l32) l32 M) (ls : ∀ l ∈ Ls, LstO 40#64 (Rg (.lst l)) l M) (dis : RgDis (AdC.live Ls) Rg)
    (inO : ∀ c, AdC.live Ls c → ∀ x, Rg c x → O x)
    (l : BitVec 64) (hl : l ∈ Ls) (M' : Mem) (l0' : TLay) (Hl0' : BitVec 64)
    (rv : TabRV D B t0 l0' Hl0' Ls M') (hl0 : Hl0'.toNat ≤ H.toNat) (kl : l0'.KL = 32#64) (sd : l0'.SD.toNat ≤ 56)
    (ph : ∀ x, TabPhys t0 l0' x → Rg .t0 x) (lo : LstO 40#64 (Rg (.lst l)) l M')
    (fr : ∀ x, x.toNat < H.toNat → ¬ Rg .t0 x → ¬ Rg (.lst l) x → M' x = M x) (hO : ∀ x, O x → x.toNat < H.toNat) :
    AdO D B O ad H M' := by
  obtain ⟨c0,c8,c16,c24,c32⟩ := cells
  have k : ∀ cc, AdC.live Ls cc → cc ≠ .t0 → cc ≠ .lst l → ∀ x, Rg cc x → M' x = M x := fun cc hc n0 nl x hx =>
    fr x (hO x (inO cc hc x hx)) (fun h => dis cc .t0 hc trivial n0 x hx h)
      (fun h => dis cc (.lst l) hc hl nl x hx h)
  have kr : ∀ x, RecW ad x → M' x = M x := fun x hx => k .recw trivial (by simp) (by simp) x (hrw x hx)
  refine ⟨t0,t8,l16,l24,l32,Ls,Rg,l0',Hl0',⟨?_,?_,?_,?_,?_⟩,hrw,⟨rv,hl0,kl,sd,ph⟩,
    tabO_frame tO (k .t8 trivial (by simp) (by simp)),lstO_frame a (k .l16 trivial (by simp) (by simp)),
    lstO_frame b (k .l24 trivial (by simp) (by simp)),lstO_frame c (k .l32 trivial (by simp) (by simp)),
    fun l' hl' => ?_,dis,inO⟩
  · rw [kr _ (Or.inl rfl)]; exact c0
  · rw [kr _ (Or.inr (Or.inl rfl))]; exact c8
  · rw [kr _ (Or.inr (Or.inr (Or.inl rfl)))]; exact c16
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact c24
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact c32
  · by_cases e : l' = l
    · subst e; exact lo
    · exact lstO_frame (ls l' hl') (k (.lst l') hl' (by simp) (by simp [e]))

#print axioms adO_stDel
end ad

/-- Locals of `remove_storage_write`. -/
def RSW (A Sl I : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "slot") = some (.val (.word Sl)) ∧
  L.lookup (ofString "idx") = some (.val (.word I))

theorem rsw_upd {A Sl I : BitVec 64} {L : GA} (h : RSW A Sl I L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "addr" ≠ x) (h2 : ofString "slot" ≠ x) (h3 : ofString "idx" ≠ x) :
    RSW A Sl I (L.update (x,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.2.2⟩

section rs
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

theorem removeStorage_aqgd (bk : BalKeep) (BA IA IS KB Ix A Sl I : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (hS : Sl.toNat % 8 = 0) (hSE : Sl.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => RSW A Sl I L ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G)
      (sourceFunctionBody Guest.guestFn_remove_storage_write) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_remove_storage_write,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  refine aqgd_of_arenaFact (Φ := H.toNat ≤ 33806089496)
    (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact (jws_heap_facts aw.1.1.1 hH1).2.1) ?_
  intro hHE
  have gba := hB1.1
  obtain ⟨lba,Hlb,rvba,hHlb,klba,_,_⟩ := bw.1 .ba trivial
  refine aqgd_decCall_htabGet_b bk BA IA IS KB Ix (LP := RSW A Sl I)
    (Pc := fun L M G => (RSW A Sl I L ∧ ∃ p val : BitVec 64,
      L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ (p ≠ 0 → val ∈ ADs)) ∧
      M = M1 ∧ G = G1)
    (Qc := fun _ _ _ => False) (ofString "m") _ _ BA A Hlb H lba ADs M1 G1 rvba hH1 hHlb hB1 Dall (Or.inl klba) hK hKE
    ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ hg ⟨la,_⟩
    have gb : s.globals.lookup (ofString "bal_accounts") = some (.val (.word BA)) := by rw [hg]; exact gba
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la,gb]
  · intro L p val la _ prop
    exact ⟨⟨rsw_upd la _ _ (by decide) (by decide) (by decide),p,val,lookup_update_eq' _ _ _,prop⟩,rfl,rfl⟩
  refine aqgd_seq (Q := fun L M G => (RSW A Sl I L ∧ ∃ p val : BitVec 64,
      L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ val ∈ ADs) ∧ M = M1 ∧ G = G1)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun L _ _ => ∃ p val : BitVec 64,
        L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ p ≠ 0)
      _ ?_ ?_ ?_) ?_
  · intro F s x H' _ _ ⟨⟨_,p,val,hm,_⟩,_,_⟩ _ ev
    refine ⟨fun _ => trivial,fun hx => ⟨p,val,hm,fun hp => ?_⟩⟩
    subst hp hx
    simp [EV,evalHOLExact,hm,Compiler.Encoders.Asm.wordCmpHOL] at ev
  · refine aqgd_return _ (fun s v H' _ hG ⟨⟨_,hM,hG1⟩,_⟩ _ ev => ?_)
    simp [EV,evalHOLExact] at ev
    subst ev
    unfold GIs at hG; subst hG
    rw [hM,hG1]
    exact ⟨rfl,balStep_refl bw hH1 hn1⟩
  · refine aqgd_conseq aqgd_skip (fun L M G ⟨⟨⟨lr,p,val,hm,prop⟩,hM,hG⟩,⟨p',val',hm',hp'⟩⟩ => ?_) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
    rw [hm] at hm'
    simp only [Option.some.injEq,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,
      HolWordLab.word.injEq,and_true] at hm'
    obtain ⟨rfl,rfl⟩ := hm'
    exact ⟨⟨lr,p,val,hm,prop hp'⟩,hM,hG⟩
  refine aqgd_conseq (P := fun L M G => ∃ p val : BitVec 64, ((RSW A Sl I L ∧
      L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)])) ∧ M = M1 ∧ G = G1) ∧ val ∈ ADs)
    (aqgd_ex (fun p => aqgd_ex (fun val => aqgd_pureE (fun had => ?_))))
    (fun L M G ⟨⟨lr,p,val,hm,had⟩,hM,hG⟩ => ⟨p,val,⟨⟨lr,hm⟩,hM,hG⟩,had⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have adv : AdO D B (Rg (.ad val)) val H M1 := bw.1 (.ad val) had
  have hbl := bw.2.2 (.ad val) had
  have hwA : ¬ Rg (.ad val) w := hwR (.ad val) had
  obtain ⟨t0,t8,l16,l24,l32,Ls,RgA,l0,Hl0,cells,hrw,⟨rv,hl,kl,sd,ph⟩,tO,a,b,c,ls,dis,inO⟩ := adv
  have vD : val.toNat < 33806089496 := by
    have := hbl _ (inO .recw trivial _ (hrw _ (Or.inl rfl))); omega
  have a0 : val + 0#64 = val := by simp
  refine aqgd_decD (Pb := fun L M G => (RSW A Sl I L ∧ L.lookup (ofString "t") = some (.val (.word t0))) ∧
      M = M1 ∧ G = G1)
    (Qb := fun _ _ _ => False) (ofString "t") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ dom _ ⟨⟨lr,lm⟩,hM,hG⟩ _ ev _
    have ea : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add [.rfield 1 (.var .local (ofString "m")),.const 0#64]) = some (.val (.word (val + 0#64))) := by
      simp [evalHOLExact,evalListHOLExact,lm,wordOpHOL,wordOp,valueIsWord,valueWord]
    unfold EV at ev
    rw [eval_load_word s _ _ t0 ea (by rw [dom.2.1,a0]; exact Dall _ vD) (by rw [hM,a0]; exact cells.1)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨⟨rsw_upd lr _ _ (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,hM,hG⟩
  refine aqgd_decCall_htabGet_b bk BA IA IS KB Ix
    (LP := fun L => RSW A Sl I L ∧ L.lookup (ofString "t") = some (.val (.word t0)))
    (Pc := fun L M G => ((RSW A Sl I L ∧ L.lookup (ofString "t") = some (.val (.word t0))) ∧
      ∃ p lv : BitVec 64, L.lookup (ofString "sl") = some (.rStruct [.val (.word p),.val (.word lv)]) ∧
        (p ≠ 0 → lv ∈ Ls)) ∧ M = M1 ∧ G = G1)
    (Qc := fun _ _ _ => False) (ofString "sl") _ _ t0 Sl Hl0 H l0 Ls M1 G1 rv hH1 hl hB1 Dall (Or.inr (Or.inl kl)) hS hSE
    ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ ⟨lr,lt⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,lt,lr.2.1]
  · intro L p lv ⟨lr,lt⟩ _ prop
    exact ⟨⟨⟨rsw_upd lr _ _ (by decide) (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact lt⟩,p,lv,lookup_update_eq' _ _ _,prop⟩,rfl,rfl⟩
  refine aqgd_seq (Q := fun L M G => ((RSW A Sl I L ∧ L.lookup (ofString "t") = some (.val (.word t0))) ∧
      ∃ p lv : BitVec 64, L.lookup (ofString "sl") = some (.rStruct [.val (.word p),.val (.word lv)]) ∧ lv ∈ Ls) ∧
      M = M1 ∧ G = G1)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun L _ _ => ∃ p lv : BitVec 64,
        L.lookup (ofString "sl") = some (.rStruct [.val (.word p),.val (.word lv)]) ∧ p ≠ 0)
      _ ?_ ?_ ?_) ?_
  · intro F s x H' _ _ ⟨⟨_,p,lv,hm,_⟩,_,_⟩ _ ev
    refine ⟨fun _ => trivial,fun hx => ⟨p,lv,hm,fun hp => ?_⟩⟩
    subst hp hx
    simp [EV,evalHOLExact,hm,Compiler.Encoders.Asm.wordCmpHOL] at ev
  · refine aqgd_return _ (fun s v H' _ hG ⟨⟨_,hM,hG1⟩,_⟩ _ ev => ?_)
    simp [EV,evalHOLExact] at ev
    subst ev
    unfold GIs at hG; subst hG
    rw [hM,hG1]
    exact ⟨rfl,balStep_refl bw hH1 hn1⟩
  · refine aqgd_conseq aqgd_skip (fun L M G ⟨⟨⟨lr,p,lv,hm,prop⟩,hM,hG⟩,⟨p',lv',hm',hp'⟩⟩ => ?_) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
    rw [hm] at hm'
    simp only [Option.some.injEq,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,
      HolWordLab.word.injEq,and_true] at hm'
    obtain ⟨rfl,rfl⟩ := hm'
    exact ⟨⟨lr,p,lv,hm,prop hp'⟩,hM,hG⟩
  refine aqgd_conseq (P := fun L M G => ∃ p lv : BitVec 64, (((RSW A Sl I L ∧
      L.lookup (ofString "t") = some (.val (.word t0))) ∧
      L.lookup (ofString "sl") = some (.rStruct [.val (.word p),.val (.word lv)])) ∧ M = M1 ∧ G = G1) ∧ lv ∈ Ls)
    (aqgd_ex (fun p => aqgd_ex (fun lv => aqgd_pureE (fun hlv => ?_))))
    (fun L M G ⟨⟨lr,p,lv,hm,hlv⟩,hM,hG⟩ => ⟨p,lv,⟨⟨lr,hm⟩,hM,hG⟩,hlv⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have lo := ls lv hlv
  have hOL : ∀ x, RgA (.lst lv) x → x.toNat < H.toNat := fun x hx => hbl x (inO (.lst lv) hlv x hx)
  have hwL : ¬ RgA (.lst lv) w := fun h => hwA (inO (.lst lv) hlv w h)
  have dTL : ∀ x, RgA .t0 x → ¬ RgA (.lst lv) x := fun x h1 h2 => dis .t0 (.lst lv) trivial hlv (by simp) x h1 h2
  refine aqgd_seq (aqgd_call_balListRemove (LP := fun L => (RSW A Sl I L ∧
      L.lookup (ofString "t") = some (.val (.word t0))) ∧
      L.lookup (ofString "sl") = some (.rStruct [.val (.word p),.val (.word lv)])) _ _ _ lv 40#64 I (RgA (.lst lv)) H
    M1 G1 lo hwL hOL hHE (by decide) Dall ?_) ?_
  · intro F s _ _ _ ⟨⟨lr,_⟩,ls_⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,ls_,lr.2.2]
  refine aqgd_ghostR (fun M3 G3 ⟨hG3,lo3,fr3⟩ => ?_)
  subst hG3
  have rv3 : TabRV D B t0 l0 Hl0 Ls M3 := tabRV_frame rv (fun x hx => fr3 x (dTL x (ph x hx)))
  refine aqgd_seq (Q := fun _ M G => G = G3 ∧ ∃ (l0' : TLay) (Hl' : BitVec 64), TabRV D B t0 l0' Hl' Ls M ∧
      Hl'.toNat ≤ H.toNat ∧ l0'.KL = 32#64 ∧ l0'.SD.toNat ≤ 56 ∧ (∀ x, TabPhys t0 l0' x → RgA .t0 x) ∧
      LstO 40#64 (RgA (.lst lv)) lv M ∧ ∀ x, ¬ RgA .t0 x → M x = M3 x)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_ ?_) ?_
  · refine aqgd_conseq (aqgd_call_htabDel_rv (LP := fun L => (RSW A Sl I L ∧
        L.lookup (ofString "t") = some (.val (.word t0))) ∧
        L.lookup (ofString "sl") = some (.rStruct [.val (.word p),.val (.word lv)])) _ _ t0 Sl Hl0 H l0 Ls M3 G3 rv3 hH1
      hl (fun h => hwA (inO .t0 trivial w (ph w h))) Dall (Or.inr (Or.inl kl)) hS hSE ?_)
      (fun _ _ _ h => h.1) (fun L M G ⟨⟨_,hG,fr⟩,N',rv4⟩ => ⟨hG,_,H,rv4,le_refl _,kl,sd,ph,
        lstO_frame lo3 (fun x hx => fr x (fun hp => dTL x (ph x hp) hx)),fun x hx => fr x (fun hp => hx (ph x hp))⟩)
      (fun _ _ _ h => h)
    intro F s _ _ _ ⟨⟨lr,lt⟩,_⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,lt,lr.2.1]
  · exact aqgd_conseq aqgd_skip (fun _ _ _ h => h.1)
      (fun L M G ⟨_,hM,hG⟩ => by subst hM hG; exact ⟨rfl,l0,Hl0,rv3,hl,kl,sd,ph,lo3,fun _ _ => rfl⟩)
      (fun _ _ _ h => h)
  refine aqgd_return _ (fun s v H'' _ hG ⟨hG',l0',Hl',rv',hl',kl',sd',ph',lo',frT⟩ _ ev => ?_)
  simp [EV,evalHOLExact] at ev
  subst ev
  unfold GIs at hG; subst hG
  rw [hG']
  have frX : ∀ x, x.toNat < H.toNat → ¬ RgA .t0 x → ¬ RgA (.lst lv) x → s.memory x = M1 x := fun x _ h0 hL =>
    (frT x h0).trans (fr3 x hL)
  refine ⟨rfl,balStep_upd bw (le_refl _) (fun _ h => h) (fun c hc x hx => Or.inl ⟨hc,hx⟩) (fun _ _ _ => rfl) (.ad val)
    had (le_refl _) (adO_sub (adO_stDel cells hrw tO a b c ls dis inO lv hlv s.memory l0' Hl' rv' hl' kl' sd' ph' lo' frX
      hbl) (fun x h => Or.inl h)) (fun x hx hn => frX x hx (fun h => hn (inO .t0 trivial x h))
      (fun h => hn (inO (.lst lv) hlv x h))) hH1 hn1⟩

#print axioms removeStorage_aqgd

end rs
end InitECandidate.Runtime
