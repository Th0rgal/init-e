import InitECandidate.Runtime.PtBalKeepGD
/-!
Declared calls keeping the block-access-list globals: `aqgd_decCallSpecDB` is `aqgd_decCallSpecD` for a callee in
`goodBal` with `BalG` carried from the call site to the continuation (the callee body keeps every `bal_*` global by
`BalKeep`). Ghost-style declared-call rules (`alloc`, `htab_new`, `lst_new`, `lst_upsert_idx`, `htab_get`) whose
continuation premise also receives `BalG` at the exit globals.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section cs
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

theorem aqgd_decCallSpecDB (bk : BalKeep) (BA IA IS KB Ix : BitVec 64)
    {P Pc Qc Q : GA → Mem → GA → Prop} {Vn' : MlS → Prop}
    (Pe : GA → Mem → GA → GA → Mem → GA → Prop) (RRe : GA → Mem → GA → ValueHOL 64 → Mem → GA → Prop)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hf : goodBal function = true) (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQGD D B A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals → s.memaddrs = D →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hshape : Vn name → shape = .one)
    (hret : ∀ L M H v M' H', P L M H → BalG BA IA IS KB Ix H' → RRe L M H v M' H' →
      shapeEqHOL (shapeOfHOLExact v) shape = true → Pc (L.update (name,v)) M' H')
    (hc : AQGD D B A w Vn Pc Qc RR cont)
    (hq : ∀ L M H L' M' H', P L M H → Qc L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQGD D B A w Vn (fun L M G => P L M G ∧ BalG BA IA IS KB Ix G) Q RR
      (.decCall name shape function arguments cont) :=
  aqgd_decCallSpecD (P := fun L M G => P L M G ∧ BalG BA IA IS KB Ix G)
    (fun L0 M0 H0 L M G => Pe L0 M0 H0 L M G ∧ BalG BA IA IS KB Ix G)
    (fun L0 M0 H0 v M' G' => RRe L0 M0 H0 v M' G' ∧ BalG BA IA IS KB Ix G')
    name function shape arguments parameters body returnShape installed allOne
    (fun L0 M0 H0 ⟨p,_⟩ => aqgd_conseq (aqgd_keepBal bk
      (List.all_eq_true.mpr (fun g hg => keepsBal_of_installed bk installed hf g hg)) (hb L0 M0 H0 p))
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h))
    (fun s values callee rs aw dom H hG ⟨pre,bg⟩ sl args lookup =>
      ⟨hpe s values callee rs aw dom H hG pre sl args lookup,bg⟩)
    hshape (fun L M H v M' H' ⟨p,_⟩ ⟨rre,bg'⟩ ok => hret L M H v M' H' p bg' rre ok) hc
    (fun L M H L' M' H' ⟨p,_⟩ qc => hq L M H L' M' H' p qc)

#print axioms aqgd_decCallSpecDB
end cs

section gc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- `aqgd_decCall_alloc_g` keeping `BalG`. -/
theorem aqgd_decCall_alloc_b (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) {LP : GA → Prop}
    {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (Nn : BitVec 64)
    {cont : ProgHOL 64} (H Nj : BitVec 64) (M1 : Mem) (G1 : GA) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hres : ∀ (L : GA) (H' : BitVec 64) (G' : GA), LP L → HeapIs G' H' → H.toNat + Nn.toNat ≤ H'.toNat →
      H'.toNat ≤ 33806089496 → H.toNat % 8 = 0 → G'.lookup (ofString "journal_n") = some (.val (.word Nj)) →
      BalG BA IA IS KB Ix G' → Pc (L.update (name,.val (.word H))) M1 G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "alloc") [.const Nn] cont) := by
  refine aqgd_conseq (P := fun L M G => (LP L ∧ M = M1 ∧ G = G1) ∧ BalG BA IA IS KB Ix G) ?_
    (fun L M G h => ⟨h,by rw [h.2.2]; exact hB1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decCallSpecDB bk BA IA IS KB Ix (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ X : BitVec 64, HeapIs G0' X ∧ (v = .val (.word X) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
        X.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ X.toNat % 8 = 0 ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup
    (by simp [goodBal,balExtra]) (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
    (fun L M G L' M' G' ⟨lp,_,_⟩ qc => hq L L' M' G' lp qc)
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    refine aqgd_conseq (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J)
      (C := C) (N := Nj) originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) Nn H M1)))
      (keepsSkBuf_of_installed originalRuntimeCode_allocation_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_allocation_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_allocation_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_allocation_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hl,hM,hG⟩
      rw [hM,hG]
      exact ⟨hn1,H,hH1,hl,rfl,rfl⟩
    · intro v M' G' ⟨hn',H',hH',eM,ev,_,_,c1,c2,_,al⟩
      exact ⟨H,hH1,⟨ev,eM,H',hH',c1,c2⟩,al,hn'⟩
  · intro F s values callee rs _ _ H' _ _ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ bg ⟨X,hX,⟨ev,eM,H',hH',c1,c2⟩,al,hn'⟩ _
    subst ev eM
    rw [hG] at hX
    have e := heapIs_unique hH1 hX
    subst e
    rw [hM]
    exact hres L H' G' lp hH' c1 c2 al hn' bg

#print axioms aqgd_decCall_alloc_b

theorem aqgd_decCall_htabNew_b (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (KL Cp : BitVec 64)
    (b : Nat) {cont : ProgHOL 64} (H Nj : BitVec 64) (M1 : Mem) (G1 : GA) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hw : w.toNat < H.toNat) (power : Cp.toNat = 2 ^ b) (kb : KL.toNat ≤ 52) (hC : 1 < Cp.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hres : ∀ (L : GA) (H' : BitVec 64) (M' : Mem) (G' : GA), LP L →
      (∀ x, x.toNat < H.toNat → M' x = M1 x) → HeapIs G' H' → H.toNat + 72 ≤ H'.toNat →
      H'.toNat ≤ 33806089496 → NewTab H H' KL Cp M' →
      TabRV D B H (newLay H KL Cp b) (allocationEnd (htabNewOrderPos H KL Cp) (Cp * 8)) ∅ M' →
      G'.lookup (ofString "journal_n") = some (.val (.word Nj)) → BalG BA IA IS KB Ix G' →
      Pc (L.update (name,.val (.word H))) M' G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "htab_new") [.const KL,.const Cp] cont) := by
  let callee : GA :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word KL))).update (ofString "cap",.val (.word Cp))
  refine aqgd_conseq (P := fun L M G => (LP L ∧ M = M1 ∧ G = G1) ∧ BalG BA IA IS KB Ix G) ?_
    (fun L M G h => ⟨h,by rw [h.2.2]; exact hB1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decCallSpecDB bk BA IA IS KB Ix (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) => L = callee ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ((∃ Tt : BitVec 64, v = .val (.word Tt) ∧ H.toNat ≤ Tt.toNat ∧
        (∀ x, x.toNat < H.toNat → M' x = M0' x) ∧ OnlyHeap G0' G' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
          Tt.toNat + 72 ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ NewTab Tt H' KL Cp M') ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj))) ∧
      (v = .val (.word H) ∧ TabRV D B H (newLay H KL Cp b) (allocationEnd (htabNewOrderPos H KL Cp) (Cp * 8)) ∅ M'))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_htabNew_lookup (by simp [goodBal,balExtra]) (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
    (fun L M G L' M' G' ⟨lp,_,_⟩ qc => hq L L' M' G' lp qc)
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G1 ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
      (fun _ _ g aw ⟨_,_,hg⟩ => by
        rw [hg] at aw; exact ⟨aw.2,(jws_heap_facts aw.1.1.1 hH1).2.1,(jws_heap_facts aw.1.1.1 hH1).2.2⟩) ?_
    intro ⟨hsc,hHE,al⟩
    have h1 := aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_htabNew_lookup
      (by decide)) (htabNew_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
        (SKB := SKB) (Nj := Nj) (w := w) KL Cp H hw M1 G1))
      (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h)
    refine aqgd_addReturnM (aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_htabNew_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_htabNew_lookup (by decide)) h1) ?_ (fun _ _ _ h => h.elim) ?_) ?_
    · intro L M G ⟨hl,hM',hG'⟩
      rw [hM',hG']
      refine ⟨⟨⟨⟨fun p hp => ?_,rfl,hH1⟩,rfl⟩,hsc⟩,hn1⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl <;> (rw [hl]; simp (config := {decide := true}) [callee,HolFiniteMapExact.lookup_update,FUPDATE])
    · intro v M' G' ⟨⟨rr,_⟩,hn'⟩
      exact ⟨rr,hn'⟩
    · intro F s code dom _ _ ⟨hl,hm,hg⟩ v post run
      have hH : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) := by rw [hg]; exact hH1
      exact newRV_ret s post KL Cp H b v hl dom.2.1 dom.2.2 code Dall hH al hHE power kb hC run
  · intro F s values callee' rs _ _ H' hG _ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact] at ev1 ev2; subst ev1 ev2
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_htabNew_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨rfl,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,_⟩ bg ⟨⟨⟨Tt,ev,hHT,fr,_,H',hH',hT,hE,nt⟩,hn'⟩,ev',rv⟩ _
    rw [ev] at ev'
    simp only [ValueHOL.val.injEq,HolWordLab.word.injEq] at ev'
    subst ev ev'
    exact hres L H' M' G' lp (fun x hx => by rw [fr x hx,hM]) hH' hT hE nt rv hn' bg

#print axioms aqgd_decCall_htabNew_b

theorem aqgd_decCall_lstNew_b (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (E Cp : BitVec 64)
    {cont : ProgHOL 64} (H Nj : BitVec 64) (M1 : Mem) (G1 : GA) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hw : w.toNat < H.toNat)
    (hres : ∀ (L : GA) (X H' : BitVec 64) (M' : Mem) (G' : GA), LP L → LNew E Cp H M1 X H' M' G' →
      G'.lookup (ofString "journal_n") = some (.val (.word Nj)) → BalG BA IA IS KB Ix G' →
      Pc (L.update (name,.val (.word X))) M' G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "lst_new") [.const E,.const Cp] cont) := by
  refine aqgd_conseq (P := fun L M G => (LP L ∧ M = M1 ∧ G = G1) ∧ BalG BA IA IS KB Ix G) ?_
    (fun L M G h => ⟨h,by rw [h.2.2]; exact hB1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decCallSpecDB bk BA IA IS KB Ix (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "cap",Cp),(ofString "esz",E)] L ∧ M = M0' ∧ G = G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (LNPost E Cp H M0' G0' v M' G' ∧ ScrIs Sc G') ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_lstNew_lookup (by simp [goodBal,balExtra]) (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
    (fun L M G L' M' G' ⟨lp,_,_⟩ qc => hq L L' M' G' lp qc)
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G1) (fun _ _ g aw ⟨⟨_,_,hg⟩,_⟩ => by rw [hg] at aw; exact aw.2) ?_
    intro hsc
    refine aqgd_conseq (P := fun L M G => (((LK [(ofString "cap",Cp),(ofString "esz",E)] L ∧ M = M1 ∧
        HeapIs G H) ∧ G = G1) ∧ ScrIs Sc G) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) ?_
      (fun L M G h => by obtain ⟨⟨lk,hM,hG⟩,jn⟩ := h; rw [hG] at jn ⊢; exact ⟨⟨⟨⟨lk,hM,hH1⟩,rfl⟩,hsc⟩,jn⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    exact aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_lstNew_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_lstNew_lookup (by decide))
      (P := fun L M G => ((LK [(ofString "cap",Cp),(ofString "esz",E)] L ∧ M = M1 ∧ HeapIs G H) ∧ G = G1) ∧
        ScrIs Sc G) (Nj := Nj)
      (aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_lstNew_lookup (by decide))
        (lstNewC_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
          (Nj := Nj) (w := w) E Cp H hw M1 G1))
        (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)))
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ _ G hG ⟨_,_,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact] at ev1 ev2; subst ev1 ev2
    have e := callee_eq originalRuntimeCode_lstNew_lookup lookup
    refine ⟨⟨fun p hp => ?_,rfl,rfl⟩,by rw [hG1]; exact hn1⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨lp,hM,_⟩ bg ⟨⟨⟨⟨X,Pp,ev,hX,hXP,hd,H',hH',hP',hE⟩,fr,_⟩,_⟩,hn'⟩ _
    subst ev
    exact hres L X H' M' G' lp ⟨hX,⟨Pp,hXP,hd,hP'⟩,hH',hE,fun x hx => by rw [fr x hx,hM]⟩ hn' bg

#print axioms aqgd_decCall_lstNew_b

theorem aqgd_decCall_lstUpsert_b (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS)
    (el eE eI : ExpHOL 64) {cont : ProgHOL 64} (Lh E I : BitVec 64) (O : BitVec 64 → Prop) (H Nj : BitVec 64)
    (M1 : Mem) (G1 : GA) (lo : LstO E O Lh M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hO : ∀ x, O x → x.toNat < H.toNat) (hwO : ¬ O w) (hwH : w.toNat < H.toNat) (hE1 : 1 ≤ E.toNat)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [el,eE,eI] =
        some [.val (.word Lh),.val (.word E),.val (.word I)])
    (hres : ∀ (L : GA) (S Hc : BitVec 64) (M' : Mem) (G' : GA), LP L → HeapIs G' Hc → H.toNat ≤ Hc.toNat →
      G'.lookup (ofString "journal_n") = some (.val (.word Nj)) →
      LstO E (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) Lh M' →
      (∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + E.toNat →
        (O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW Lh x) →
      (∀ x, x.toNat < H.toNat → ¬ O x → M' x = M1 x) → BalG BA IA IS KB Ix G' →
      Pc (L.update (name,.val (.word S))) M' G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "lst_upsert_idx") [el,eE,eI] cont) := by
  obtain ⟨P,N,Cp,hd,hNC,hC0,al,hHd,hBuf⟩ := lo
  have hHl : H.toNat < 2 ^ 64 := H.isLt
  have hCE : 0 < E.toNat * Cp.toNat := Nat.mul_pos (by omega) hC0
  have hbuf : P.toNat + E.toNat * Cp.toNat ≤ H.toNat :=
    buf_le P.isLt hHl hCE (fun x l u => hO x (hBuf x l u).1)
  refine aqgd_conseq (P := fun L M G => (LP L ∧ M = M1 ∧ G = G1) ∧ BalG BA IA IS KB Ix G) ?_
    (fun L M G h => ⟨h,by rw [h.2.2]; exact hB1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decCallSpecDB bk BA IA IS KB Ix (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "l",Lh),(ofString "esz",E),(ofString "idx",I)] L ∧ M = M0' ∧ G = G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (LUPost Lh E P N Cp H M0' G0' v M' G' ∧ ScrIs Sc G') ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_lstUpsertIdx_lookup (by simp [goodBal,balExtra]) (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
    (fun L M G L' M' G' ⟨lp,_,_⟩ qc => hq L L' M' G' lp qc)
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G1 ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
      (fun _ _ g aw ⟨⟨_,_,hg⟩,_⟩ => by
        rw [hg] at aw; exact ⟨aw.2,(jws_heap_facts aw.1.1.1 hH1).2.1,(jws_heap_facts aw.1.1.1 hH1).2.2⟩) ?_
    intro ⟨hsc,hHE,hal⟩
    have hsz : E.toNat * Cp.toNat * 2 < 2 ^ 64 := by omega
    have hwh : ¬ HdW Lh w := fun h => hwO (hHd w h)
    have hwB : ¬ (P.toNat ≤ w.toNat ∧ w.toNat < P.toNat + E.toNat * Cp.toNat) := fun ⟨a,b⟩ => hwO (hBuf w a b).1
    refine aqgd_conseq (P := fun L M G => (((LK [(ofString "l",Lh),(ofString "esz",E),(ofString "idx",I)] L ∧ M = M1 ∧
        HeapIs G H) ∧ G = G1) ∧ ScrIs Sc G) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) ?_
      (fun L M G h => by obtain ⟨⟨lk,hM,hG⟩,jn⟩ := h; rw [hG]; exact ⟨⟨⟨⟨lk,hM,by rw [← hG]; rw [hG]; exact hH1⟩,rfl⟩,hsc⟩,
        by rw [← hG]; exact jn⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_lstUpsertIdx_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_lstUpsertIdx_lookup (by decide))
      (P := fun L M G => ((LK [(ofString "l",Lh),(ofString "esz",E),(ofString "idx",I)] L ∧ M = M1 ∧ HeapIs G H) ∧
        G = G1) ∧ ScrIs Sc G) (Nj := Nj)
      (aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_lstUpsertIdx_lookup (by decide))
        (lstUpsertIdx_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
          (SKB := SKB) (Nj := Nj) (w := w) Lh E I P N Cp H M1 G1 (by omega) hwH hwh hd hNC hC0 hE1 hbuf hsz hwB
          (fun x l u => (hBuf x l u).2)))
        (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)))
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ dom H' hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_three_word_lookup _ _ (ofString "l") (ofString "esz") (ofString "idx") _ _ _ _ (by decide) (by decide)
      (by decide) originalRuntimeCode_lstUpsertIdx_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨fun p hp => ?_,rfl,rfl⟩,by rw [hG1]; exact hn1⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨lp,hM,_⟩ bg ⟨⟨⟨_,S,Pn,Nn,Cn,Hc,ev,hd',hHc,le,hNn,hCn,hPn,⟨j,hj,hS⟩,old,_,fr⟩,_⟩,hn'⟩ _
    subst ev hM
    have bufN : ∀ x : BitVec 64, Pn.toNat ≤ x.toNat → x.toNat < Pn.toNat + E.toNat * Cn.toNat →
        (O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW Lh x := by
      intro x l u
      rcases old with ⟨rfl,rfl⟩ | ⟨hp,_⟩
      · exact ⟨Or.inl (hBuf x l u).1,(hBuf x l u).2⟩
      · refine ⟨Or.inr ⟨by omega,by omega⟩,fun h => ?_⟩
        have := hO x (hHd x h); omega
    have alN : Lh.toNat + 24 ≤ Pn.toNat := by
      rcases old with ⟨rfl,rfl⟩ | ⟨hp,_⟩
      · exact al
      · omega
    refine hres L S Hc M' G' lp hHc le hn' ⟨Pn,Nn,Cn,hd',hNn,hCn,alN,fun x h => Or.inl (hHd x h),bufN⟩
      (fun x l u => bufN x (elem_in hj hNn hS x.toNat l u).1 (elem_in hj hNn hS x.toNat l u).2) ?_ bg
    intro x hx ho
    refine fr x hx (fun h => ho (hHd x h)) (fun e => ?_)
    rw [e] at hx ho
    have hin := elem_in hj hNn hS S.toNat (le_refl _) (by omega)
    rcases bufN S hin.1 hin.2 with ⟨h | ⟨h,_⟩,_⟩
    · exact ho h
    · omega

#print axioms aqgd_decCall_lstUpsert_b

theorem aqgd_decCall_htabGet_b (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (et ek : ExpHOL 64)
    {cont : ProgHOL 64} (T K Hl Hc : BitVec 64) (l : TLay) (S : Set (BitVec 64)) (M1 : Mem) (G1 : GA)
    (rv : TabRV D B T l Hl S M1) (hH1 : HeapIs G1 Hc) (hHl : Hl.toNat ≤ Hc.toNat) (hB1 : BalG BA IA IS KB Ix G1)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (sup : l.KL = 20 ∨ l.KL = 32 ∨ l.KL = 52) (hK : K.toNat % 8 = 0) (hKE : K.toNat + 52 ≤ 33806089496)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek] =
        some [.val (.word T),.val (.word K)])
    (hshape : Vn name → ShapeHOL.comb [.one,.one] = .one)
    (hres : ∀ (L : GA) (p val : BitVec 64), LP L → (p = 0 ∨ p = 1) → (p ≠ 0 → val ∈ S) →
      Pc (L.update (name,.rStruct [.val (.word p),.val (.word val)])) M1 G1)
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name (.comb [.one,.one]) (ofString "htab_get") [et,ek] cont) := by
  refine aqgd_conseq (P := fun L M G => (LP L ∧ M = M1 ∧ G = G1) ∧ BalG BA IA IS KB Ix G) ?_
    (fun L M G h => ⟨h,by rw [h.2.2]; exact hB1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decCallSpecDB bk BA IA IS KB Ix (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "t") = some (.val (.word T)) ∧
      L.lookup (ofString "key") = some (.val (.word K))) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' v M' G' => (M' = M0' ∧ G' = G0') ∧ ∃ p val : BitVec 64,
      v = .rStruct [.val (.word p),.val (.word val)] ∧ (p = 0 ∨ p = 1) ∧ (p ≠ 0 → val ∈ S))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup
    (by simp only [goodBal,show goodGA (ofString "htab_get") = true by decide,Bool.true_or]) (by simp) ?_ ?_ hshape ?_ hc ?_
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    refine aqgd_addReturn (aqgd_conseq (aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0') (fun _ _ _ h => h.2) (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h)) ?_
    intro F s code dom aw _ ⟨⟨tl,kl⟩,sm,sg⟩ v post run
    have hH : HeapIs s.globals Hc := by rw [sg,hG]; exact hH1
    have hf := jws_heap_facts aw.1.1.1 hH
    exact getRV_ret s post T K Hc Hl l S v dom.2.1 dom.2.2 code Dall (by rw [sm,hM]; exact rv) hH hHl hf.2.1 hf.2.2
      sup hK hKE tl kl run
  · intro F s values callee rs _ dom H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_two_word_lookup_shape _ _ (ofString "t") (ofString "key") _ _ _ _ (by decide)
      originalRuntimeCode_hashGet_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ _ ⟨⟨eM,eG⟩,p,val,ev,bool,prop⟩ _
    rw [eM,eG,hM,hG,ev]
    exact hres L p val lp bool prop
  · intro L M G L' M' G' ⟨lp,_,_⟩ qc
    exact hq L L' M' G' lp qc

#print axioms aqgd_decCall_htabGet_b
theorem aqgd_decCall_lstPush_b (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS)
    (el eE : ExpHOL 64) {cont : ProgHOL 64} (Lh E : BitVec 64) (O : BitVec 64 → Prop) (H Nj : BitVec 64)
    (M1 : Mem) (G1 : GA) (lo : LstO E O Lh M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hO : ∀ x, O x → x.toNat < H.toNat) (hwO : ¬ O w) (hwH : w.toNat < H.toNat) (hE1 : 1 ≤ E.toNat)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [el,eE] =
        some [.val (.word Lh),.val (.word E)])
    (hres : ∀ (L : GA) (S Hc : BitVec 64) (M' : Mem) (G' : GA), LP L → HeapIs G' Hc → H.toNat ≤ Hc.toNat →
      G'.lookup (ofString "journal_n") = some (.val (.word Nj)) →
      LstO E (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) Lh M' →
      (∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + E.toNat →
        (O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW Lh x) →
      (∀ x, x.toNat < H.toNat → ¬ O x → M' x = M1 x) → BalG BA IA IS KB Ix G' →
      Pc (L.update (name,.val (.word S))) M' G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "lst_push") [el,eE] cont) := by
  obtain ⟨P,N,Cp,hd,hNC,hC0,al,hHd,hBuf⟩ := lo
  have hHl : H.toNat < 2 ^ 64 := H.isLt
  have hCE : 0 < E.toNat * Cp.toNat := Nat.mul_pos (by omega) hC0
  have hbuf : P.toNat + E.toNat * Cp.toNat ≤ H.toNat :=
    buf_le P.isLt hHl hCE (fun x l u => hO x (hBuf x l u).1)
  refine aqgd_conseq (P := fun L M G => (LP L ∧ M = M1 ∧ G = G1) ∧ BalG BA IA IS KB Ix G) ?_
    (fun L M G h => ⟨h,by rw [h.2.2]; exact hB1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decCallSpecDB bk BA IA IS KB Ix (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M0' ∧ G = G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (LPPost Lh E P N Cp H M0' G0' v M' G' ∧ ScrIs Sc G') ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_lstPush_lookup (by simp [goodBal,balExtra]) (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
    (fun L M G L' M' G' ⟨lp,_,_⟩ qc => hq L L' M' G' lp qc)
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G1 ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
      (fun _ _ g aw ⟨⟨_,_,hg⟩,_⟩ => by
        rw [hg] at aw; exact ⟨aw.2,(jws_heap_facts aw.1.1.1 hH1).2.1,(jws_heap_facts aw.1.1.1 hH1).2.2⟩) ?_
    intro ⟨hsc,hHE,hal⟩
    have hsz : E.toNat * Cp.toNat * 2 < 2 ^ 64 := by omega
    have hwh : ¬ HdW Lh w := fun h => hwO (hHd w h)
    have hwB : ¬ (P.toNat ≤ w.toNat ∧ w.toNat < P.toNat + E.toNat * Cp.toNat) := fun ⟨a,b⟩ => hwO (hBuf w a b).1
    refine aqgd_conseq (P := fun L M G => (((LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M1 ∧
        HeapIs G H) ∧ G = G1) ∧ ScrIs Sc G) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) ?_
      (fun L M G h => by obtain ⟨⟨lk,hM,hG⟩,jn⟩ := h; rw [hG]; exact ⟨⟨⟨⟨lk,hM,by rw [← hG]; rw [hG]; exact hH1⟩,rfl⟩,hsc⟩,
        by rw [← hG]; exact jn⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_lstPush_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_lstPush_lookup (by decide))
      (P := fun L M G => ((LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M1 ∧ HeapIs G H) ∧
        G = G1) ∧ ScrIs Sc G) (Nj := Nj)
      (aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_lstPush_lookup (by decide))
        (lstPush_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
          (SKB := SKB) (Nj := Nj) (w := w) Lh E P N Cp H M1 G1 (by omega) hwH hwh hd hNC hC0 hE1 hbuf hsz))
        (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)))
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ dom H' hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_two_word_lookup _ _ (ofString "l") (ofString "esz") _ _ _ (by decide)
      originalRuntimeCode_lstPush_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨fun p hp => ?_,rfl,rfl⟩,by rw [hG1]; exact hn1⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨lp,hM,_⟩ bg ⟨⟨⟨fr,_,Pn,Cn,Hc,ev,hd',hHc,le,hNC',hPn,old⟩,_⟩,hn'⟩ _
    subst ev hM
    have hCnE : Cn.toNat ≤ E.toNat * Cn.toNat := Nat.le_mul_of_pos_left _ (by omega)
    have bufN : ∀ x : BitVec 64, Pn.toNat ≤ x.toNat → x.toNat < Pn.toNat + E.toNat * Cn.toNat →
        (O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW Lh x := by
      intro x l u
      rcases old with ⟨rfl,rfl⟩ | ⟨hp,_⟩
      · exact ⟨Or.inl (hBuf x l u).1,(hBuf x l u).2⟩
      · refine ⟨Or.inr ⟨by omega,by omega⟩,fun h => ?_⟩
        have := hO x (hHd x h); omega
    have alN : Lh.toNat + 24 ≤ Pn.toNat := by
      rcases old with ⟨rfl,rfl⟩ | ⟨hp,_⟩
      · exact al
      · omega
    have eN1 : (N + 1#64).toNat = N.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    have m : N.toNat * E.toNat ≤ Cn.toNat * E.toNat := Nat.mul_le_mul_right _ (by omega)
    have eS : (Pn + N * E).toNat = Pn.toNat + N.toNat * E.toNat := by
      rw [Nat.mul_comm E.toNat Cn.toNat] at hPn
      exact itm_toNat_add_mul Pn N E (by have := Hc.isLt; omega)
    refine hres L (Pn + N * E) Hc M' G' lp hHc le hn' ⟨Pn,N + 1#64,Cn,hd',by rw [eN1]; omega,by omega,alN,
      fun x h => Or.inl (hHd x h),bufN⟩
      (fun x l u => bufN x (elem_in (j := N.toNat) (Nn := N.toNat + 1) (Nat.lt_succ_self _) hNC' eS x.toNat l u).1
        (elem_in (j := N.toNat) (Nn := N.toNat + 1) (Nat.lt_succ_self _) hNC' eS x.toNat l u).2)
      (fun x hx ho => fr x hx (fun h => ho (hHd x h))) bg

#print axioms aqgd_decCall_lstPush_b
end gc
end InitECandidate.Runtime
