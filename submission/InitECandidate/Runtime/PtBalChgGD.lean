import InitECandidate.Runtime.PtBalAddGD
/-!
The actual `add_balance_change(addr, idx, post_balance)`: ensure the account record, upsert the transaction index into
its balance list and store the four balance words into the element; the block-access-list state steps from the entry.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An owned list depends on memory only through its header words. -/
theorem lstO_frame_hdr {E Lh : BitVec 64} {O : BitVec 64 → Prop} {M M' : Mem} (h : LstO E O Lh M)
    (keep : ∀ x, HdW Lh x → M' x = M x) : LstO E O Lh M' := by
  obtain ⟨P,N,Cp,⟨h0,h8,h16⟩,a,b,c,hh,hb⟩ := h
  refine ⟨P,N,Cp,⟨?_,?_,?_⟩,a,b,c,hh,hb⟩
  · rw [keep _ (Or.inl rfl)]; exact h0
  · rw [keep _ (Or.inr (Or.inl rfl))]; exact h8
  · rw [keep _ (Or.inr (Or.inr rfl))]; exact h16

section ab
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- Locals of `add_balance_change`. -/
def ABL (A I b0 b1 b2 b3 : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "idx") = some (.val (.word I)) ∧
  L.lookup (ofString "post_balance") = some (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)])

theorem abl_upd {A I b0 b1 b2 b3 : BitVec 64} {L : GA} (h : ABL A I b0 b1 b2 b3 L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "addr" ≠ x) (h2 : ofString "idx" ≠ x) (h3 : ofString "post_balance" ≠ x) :
    ABL A I b0 b1 b2 b3 (L.update (x,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.2.2⟩

theorem addBalance_aqgd (bk : BalKeep) (BA IA IS KB Ix A I b0 b1 b2 b3 : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ABL A I b0 b1 b2 b3 L ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G)
      (sourceFunctionBody Guest.guestFn_add_balance_change) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_add_balance_change,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  refine aqgd_decCall_balEnsure bk BA IA IS KB Ix A ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hwP p0 hK hKE Dall
    (LP := ABL A I b0 b1 b2 b3)
    (Pc := fun L M G => ∃ ad : BitVec 64, (ABL A I b0 b1 b2 b3 L ∧ L.lookup (ofString "ad") = some (.val (.word ad))) ∧
      (BalStepA D B BA IA IS KB ADs Rg H Nj M1 ad M G ∧ BalG BA IA IS KB Ix G))
    (Qc := fun _ _ _ => False) (ofString "ad") _ ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ ⟨la,_,_⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la]
  · intro L ad M' G' lp st bg
    exact ⟨ad,⟨abl_upd lp _ _ (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,st,bg⟩
  refine aqgd_ex (fun ad => aqgd_ghostR (fun M2 G2 ⟨⟨ADs',Rg',H',hH',le,hn',bw',sub,gr,fr,had⟩,bg⟩ => ?_))
  have adv : AdO D B (Rg' (.ad ad)) ad H' M2 := bw'.1 (.ad ad) had
  have hbl := bw'.2.2 (.ad ad) had
  obtain ⟨l,R,cell,lo,hR,upd⟩ := adO_lst16 adv
  have hwO : ¬ R w := fun h => by
    rcases gr (.ad ad) had w (hR w h) with ⟨l1,h1⟩ | ⟨h1,_⟩
    · exact hwR _ l1 h1
    · omega
  have hO : ∀ x, R x → x.toNat < H'.toNat := fun x hx => hbl x (hR x hx)
  refine aqgd_of_arenaFact (Φ := H'.toNat ≤ 33806089496 ∧ H'.toNat % 8 = 0)
    (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact (jws_heap_facts aw.1.1.1 hH').2) ?_
  intro ⟨hHE,hHal'⟩
  have c16D : (ad + 16#64).toNat < 33806089496 := by
    obtain ⟨_,_,_,_,_,_,RgA,_,_,_,hrw,_,_,_,_,_,_,_,inO⟩ := adv
    have := hbl _ (inO .recw trivial _ (hrw _ (Or.inr (Or.inr (Or.inl rfl))))); omega
  refine aqgd_decCall_lstUpsert_b bk BA IA IS KB Ix
    (LP := fun L => ABL A I b0 b1 b2 b3 L ∧ L.lookup (ofString "ad") = some (.val (.word ad)))
    (Pc := fun L M G => ∃ S Hc : BitVec 64, ((ABL A I b0 b1 b2 b3 L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧
        L.lookup (ofString "e") = some (.val (.word S))) ∧
      LstO 40#64 (fun x => R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) l M ∧
      (∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + 40 →
        (R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW l x) ∧
      (∀ x, x.toNat < H'.toNat → ¬ R x → M x = M2 x)) ∧ HeapIs G Hc ∧ H'.toNat ≤ Hc.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G)
    (Qc := fun _ _ _ => False) (ofString "e") _ _ _ l 40#64 I R H' Nj M2 G2 lo hH' hn' bg hO hwO (by omega) (by decide)
    hHal' ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s hd hm _ ⟨⟨_,li,_⟩,lad⟩
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact,eval_record_word s .local (ofString "ad") ad 16#64 l (by simp [evalHOLExact,lad])
      (by rw [hd]; exact Dall _ c16D) (by rw [hm]; exact cell)]
    simp [evalHOLExact,li]
  · intro L S Hc M' G' ⟨lp,lad⟩ hHc le' hn'' lo' el fr' bg'
    exact ⟨S,Hc,⟨⟨abl_upd lp _ _ (by decide) (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact lad,
      lookup_update_eq' _ _ _⟩,lo',fun x l u => el x l (by simpa using u),fr'⟩,hHc,le',hn'',bg'⟩
  refine aqgd_ex (fun S => aqgd_ex (fun Hc => ?_))
  refine aqgd_of_arenaFact (Φ := Hc.toNat ≤ 33806089496)
    (fun _ _ g aw ⟨_,hH,_⟩ => (jws_heap_facts aw.1.1.1 hH).2.1) ?_
  intro hcE
  have hS : S.toNat < Hc.toNat ∨ True := Or.inr trivial
  refine aqgd_seq (aqgd_storeV (Q := fun L M G => ((ABL A I b0 b1 b2 b3 L ∧
      L.lookup (ofString "ad") = some (.val (.word ad))) ∧
      LstO 40#64 (fun x => R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) l M ∧
      (∀ x, x.toNat < H'.toNat → ¬ R x → M x = M2 x)) ∧ HeapIs G Hc ∧ H'.toNat ≤ Hc.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj))) _ _
    (fun s _ _ ⟨⟨⟨lp,lad,le_⟩,lo',el,fr'⟩,hHc,le',hn'',_⟩ => ?_)) ?_
  · have S0 := el S (le_refl _) (by omega)
    have Sb : S.toNat < Hc.toNat := by
      rcases S0.1 with h | ⟨_,h⟩
      · have := hO S h; omega
      · exact h
    have ew : ∀ j : Nat, j < 4 → (S + 8#64 + BitVec.ofNat 64 (8 * j)).toNat = S.toNat + 8 + 8 * j := fun j hj => by
      rw [BitVec.toNat_add,BitVec.toNat_add]; simp; omega
    refine ⟨S + 8#64,4,by simp [EV,evalHOLExact,evalListHOLExact,le_,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun x hx => ?_,fun j hj e => ?_,fun M' hM' => ⟨⟨⟨lp,lad⟩,lstO_frame_hdr lo' (fun x hx => ?_),fun x hx hr => ?_⟩,
        hHc,le',hn''⟩⟩
    · simp [EV,evalHOLExact,lp.2.2] at hx
      subst hx; simp [flattenHOL]
    · have := el (S + 8#64 + BitVec.ofNat 64 (8 * j)) (by rw [ew j hj]; omega) (by rw [ew j hj]; omega)
      rw [← e] at this
      rcases this.1 with h | ⟨h,_⟩
      · exact hwO h
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
  refine aqgd_return _ (fun s v H'' _ hG ⟨⟨⟨_,_⟩,lo',fr'⟩,hHc,le',hn''⟩ _ ev => ?_)
  simp [EV,evalHOLExact] at ev
  subst ev
  refine ⟨rfl,balStep_upd bw' le sub gr fr (.ad ad) had le' (upd s.memory Hc le' lo' fr' hbl) (fun x hx hr => fr' x hx
    (fun h => hr (hR x h))) ?_ ?_⟩
  · exact hHc
  · exact hn''

#print axioms addBalance_aqgd

/-- Locals of `add_code_change`. -/
def ACL (A I Cd Cl : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "idx") = some (.val (.word I)) ∧
  L.lookup (ofString "code") = some (.val (.word Cd)) ∧ L.lookup (ofString "code_len") = some (.val (.word Cl))

theorem acl_upd {A I Cd Cl : BitVec 64} {L : GA} (h : ACL A I Cd Cl L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "addr" ≠ x) (h2 : ofString "idx" ≠ x) (h3 : ofString "code" ≠ x) (h4 : ofString "code_len" ≠ x) :
    ACL A I Cd Cl (L.update (x,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.2.2.1,by rw [lookup_update_ne' _ _ h4]; exact h.2.2.2⟩

theorem addCode_aqgd (bk : BalKeep) (BA IA IS KB Ix A I Cd Cl : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ACL A I Cd Cl L ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G)
      (sourceFunctionBody Guest.guestFn_add_code_change) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_add_code_change,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  refine aqgd_decCall_balEnsure bk BA IA IS KB Ix A ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hwP p0 hK hKE Dall
    (LP := ACL A I Cd Cl)
    (Pc := fun L M G => ∃ ad : BitVec 64, (ACL A I Cd Cl L ∧ L.lookup (ofString "ad") = some (.val (.word ad))) ∧
      (BalStepA D B BA IA IS KB ADs Rg H Nj M1 ad M G ∧ BalG BA IA IS KB Ix G))
    (Qc := fun _ _ _ => False) (ofString "ad") _ ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ ⟨la,_,_⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la]
  · intro L ad M' G' lp st bg
    exact ⟨ad,⟨acl_upd lp _ _ (by decide) (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,st,bg⟩
  refine aqgd_ex (fun ad => aqgd_ghostR (fun M2 G2 ⟨⟨ADs',Rg',H',hH',le,hn',bw',sub,gr,fr,had⟩,bg⟩ => ?_))
  have adv : AdO D B (Rg' (.ad ad)) ad H' M2 := bw'.1 (.ad ad) had
  have hbl := bw'.2.2 (.ad ad) had
  obtain ⟨l,R,cell,lo,hR,upd⟩ := adO_lst32 adv
  have hwO : ¬ R w := fun h => by
    rcases gr (.ad ad) had w (hR w h) with ⟨l1,h1⟩ | ⟨h1,_⟩
    · exact hwR _ l1 h1
    · omega
  have hO : ∀ x, R x → x.toNat < H'.toNat := fun x hx => hbl x (hR x hx)
  refine aqgd_of_arenaFact (Φ := H'.toNat ≤ 33806089496 ∧ H'.toNat % 8 = 0)
    (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact (jws_heap_facts aw.1.1.1 hH').2) ?_
  intro ⟨hHE,hHal'⟩
  have c16D : (ad + 32#64).toNat < 33806089496 := by
    obtain ⟨_,_,_,_,_,_,RgA,_,_,_,hrw,_,_,_,_,_,_,_,inO⟩ := adv
    have := hbl _ (inO .recw trivial _ (hrw _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))); omega
  refine aqgd_decCall_lstUpsert_b bk BA IA IS KB Ix
    (LP := fun L => ACL A I Cd Cl L ∧ L.lookup (ofString "ad") = some (.val (.word ad)))
    (Pc := fun L M G => ∃ S Hc : BitVec 64, ((ACL A I Cd Cl L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧
        L.lookup (ofString "e") = some (.val (.word S))) ∧
      LstO 24#64 (fun x => R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) l M ∧
      (∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + 24 →
        (R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW l x) ∧
      (∀ x, x.toNat < H'.toNat → ¬ R x → M x = M2 x)) ∧ HeapIs G Hc ∧ H'.toNat ≤ Hc.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G)
    (Qc := fun _ _ _ => False) (ofString "e") _ _ _ l 24#64 I R H' Nj M2 G2 lo hH' hn' bg hO hwO (by omega) (by decide)
    hHal' ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s hd hm _ ⟨⟨_,li,_⟩,lad⟩
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact,eval_record_word s .local (ofString "ad") ad 32#64 l (by simp [evalHOLExact,lad])
      (by rw [hd]; exact Dall _ c16D) (by rw [hm]; exact cell)]
    simp [evalHOLExact,li]
  · intro L S Hc M' G' ⟨lp,lad⟩ hHc le' hn'' lo' el fr' bg'
    exact ⟨S,Hc,⟨⟨acl_upd lp _ _ (by decide) (by decide) (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact lad,
      lookup_update_eq' _ _ _⟩,lo',fun x l u => el x l (by simpa using u),fr'⟩,hHc,le',hn'',bg'⟩
  refine aqgd_ex (fun S => aqgd_ex (fun Hc => ?_))
  refine aqgd_of_arenaFact (Φ := Hc.toNat ≤ 33806089496)
    (fun _ _ g aw ⟨_,hH,_⟩ => (jws_heap_facts aw.1.1.1 hH).2.1) ?_
  intro hcE
  have hS : S.toNat < Hc.toNat ∨ True := Or.inr trivial
  have SB : ∀ x : BitVec 64, x = S + 8#64 ∨ x = S + 16#64 → True := fun _ _ => trivial
  refine aqgd_seq (aqgd_storeW (Q := fun L M G => ((ACL A I Cd Cl L ∧ L.lookup (ofString "ad") = some (.val (.word ad)) ∧
        L.lookup (ofString "e") = some (.val (.word S))) ∧
      LstO 24#64 (fun x => R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) l M ∧
      (∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + 24 →
        (R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW l x) ∧
      (∀ x, x.toNat < H'.toNat → ¬ R x → M x = M2 x)) ∧ HeapIs G Hc ∧ H'.toNat ≤ Hc.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj))) _ _
    (fun s _ _ ⟨⟨⟨lp,lad,le_⟩,lo',el,fr'⟩,hHc,le',hn'',_⟩ => ?_)) ?_
  · have S0 := el S (le_refl _) (by omega)
    have Sb : S.toNat < Hc.toNat := by
      rcases S0.1 with h | ⟨_,h⟩
      · have := hO S h; omega
      · exact h
    have e8 : (S + 8#64).toNat = S.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    have W := el (S + 8#64) (by rw [e8]; omega) (by rw [e8]; omega)
    refine ⟨S + 8#64,Cd,by simp [EV,evalHOLExact,evalListHOLExact,le_,wordOpHOL,wordOp,valueIsWord,valueWord],
      by simp [EV,evalHOLExact,lp.2.2.1],fun e => ?_,⟨⟨lp,lad,le_⟩,lstO_frame_hdr lo' (fun x hx => ?_),el,
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
  refine aqgd_seq (aqgd_storeW (Q := fun L M G => ((ACL A I Cd Cl L ∧
      L.lookup (ofString "ad") = some (.val (.word ad))) ∧
      LstO 24#64 (fun x => R x ∨ (H'.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) l M ∧
      (∀ x, x.toNat < H'.toNat → ¬ R x → M x = M2 x)) ∧ HeapIs G Hc ∧ H'.toNat ≤ Hc.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj))) _ _
    (fun s _ _ ⟨⟨⟨lp,lad,le_⟩,lo',el,fr'⟩,hHc,le',hn''⟩ => ?_)) ?_
  · have S0 := el S (le_refl _) (by omega)
    have Sb : S.toNat < Hc.toNat := by
      rcases S0.1 with h | ⟨_,h⟩
      · have := hO S h; omega
      · exact h
    have e16 : (S + 16#64).toNat = S.toNat + 16 := by rw [BitVec.toNat_add]; simp; omega
    have W := el (S + 16#64) (by rw [e16]; omega) (by rw [e16]; omega)
    refine ⟨S + 16#64,Cl,by simp [EV,evalHOLExact,evalListHOLExact,le_,wordOpHOL,wordOp,valueIsWord,valueWord],
      by simp [EV,evalHOLExact,lp.2.2.2],fun e => ?_,⟨⟨lp,lad⟩,lstO_frame_hdr lo' (fun x hx => ?_),
        fun x hx hr => ?_⟩,hHc,le',hn''⟩
    · rw [← e] at W
      rcases W.1 with h | ⟨h,_⟩
      · exact hwO h
      · omega
    · have : x ≠ S + 16#64 := fun e => W.2 (e ▸ hx)
      simp only [if_neg this]
    · have : x ≠ S + 16#64 := fun e => by
        rw [e] at hx hr
        rcases W.1 with h | ⟨h,_⟩
        · exact hr h
        · omega
      simp only [if_neg this]; exact fr' x hx hr
  refine aqgd_return _ (fun s v H'' _ hG ⟨⟨⟨_,_⟩,lo',fr'⟩,hHc,le',hn''⟩ _ ev => ?_)
  simp [EV,evalHOLExact] at ev
  subst ev
  exact ⟨rfl,balStep_upd bw' le sub gr fr (.ad ad) had le' (upd s.memory Hc le' lo' fr' hbl) (fun x hx hr => fr' x hx
    (fun h => hr (hR x h))) hHc hn''⟩

#print axioms addCode_aqgd
end ab
end InitECandidate.Runtime
