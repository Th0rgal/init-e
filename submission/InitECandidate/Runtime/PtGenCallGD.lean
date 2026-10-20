import InitECandidate.Runtime.PtBalObjGD
/-!
State-agnostic call rules at the `JWSBUS` arena, with the call-site memory and globals fixed as ghosts: declared
`alloc(n)`, declared `htab_new(KL, Cp)`, declared and assigning `lst_new(esz, cap)`. Each continuation premise receives
the callee's exit facts (fresh object at or above the heap pointer at the call, memory below it kept, the journal
counter kept).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section gc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `var 1 name = alloc(Nn)`. -/
theorem aqgd_decCall_alloc_g {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (Nn : BitVec 64)
    {cont : ProgHOL 64} (H Nj : BitVec 64) (M1 : Mem) (G1 : GA) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (hres : ∀ (L : GA) (H' : BitVec 64) (G' : GA), LP L → HeapIs G' H' → H.toNat + Nn.toNat ≤ H'.toNat →
      H'.toNat ≤ 33806089496 → H.toNat % 8 = 0 → G'.lookup (ofString "journal_n") = some (.val (.word Nj)) →
      Pc (L.update (name,.val (.word H))) M1 G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "alloc") [.const Nn] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ X : BitVec 64, HeapIs G0' X ∧ (v = .val (.word X) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
        X.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ X.toNat % 8 = 0 ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
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
  · intro F s values callee rs _ H' _ _ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨X,hX,⟨ev,eM,H',hH',c1,c2⟩,al,hn'⟩ _
    subst ev eM
    rw [hG] at hX
    have e := heapIs_unique hH1 hX
    subst e
    rw [hM]
    exact hres L H' G' lp hH' c1 c2 al hn'

#print axioms aqgd_decCall_alloc_g

/-- The actual `var 1 name = htab_new(KL, Cp)`. -/
theorem aqgd_decCall_htabNew_g {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (KL Cp : BitVec 64)
    {cont : ProgHOL 64} (H Nj : BitVec 64) (M1 : Mem) (G1 : GA) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hw : w.toNat < H.toNat)
    (hres : ∀ (L : GA) (Tt H' : BitVec 64) (M' : Mem) (G' : GA), LP L → H.toNat ≤ Tt.toNat →
      (∀ x, x.toNat < H.toNat → M' x = M1 x) → HeapIs G' H' → Tt.toNat + 72 ≤ H'.toNat →
      H'.toNat ≤ 33806089496 → NewTab Tt H' KL Cp M' → G'.lookup (ofString "journal_n") = some (.val (.word Nj)) →
      Pc (L.update (name,.val (.word Tt))) M' G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "htab_new") [.const KL,.const Cp] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      LK [(ofString "cap",Cp),(ofString "key_len",KL)] L ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (∃ Tt : BitVec 64, v = .val (.word Tt) ∧ H.toNat ≤ Tt.toNat ∧
        (∀ x, x.toNat < H.toNat → M' x = M0' x) ∧ OnlyHeap G0' G' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
          Tt.toNat + 72 ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ NewTab Tt H' KL Cp M') ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_htabNew_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
    (fun L M G L' M' G' ⟨lp,_,_⟩ qc => hq L L' M' G' lp qc)
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G1) (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact aw.2) ?_
    intro hsc
    have h1 := aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_htabNew_lookup
      (by decide)) (htabNew_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
        (SKB := SKB) (Nj := Nj) (w := w) KL Cp H hw M1 G1))
      (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_htabNew_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_htabNew_lookup (by decide)) h1) ?_ (fun _ _ _ h => h.elim) ?_
    · intro L M G ⟨lk,hM',hG'⟩
      rw [hM',hG']
      exact ⟨⟨⟨⟨lk,rfl,hH1⟩,rfl⟩,hsc⟩,hn1⟩
    · intro v M' G' ⟨⟨rr,_⟩,hn'⟩
      exact ⟨rr,hn'⟩
  · intro F s values callee rs _ H' hG _ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact] at ev1 ev2; subst ev1 ev2
    have e := callee_eq originalRuntimeCode_htabNew_lookup lookup
    refine ⟨fun p hp => ?_,rfl,rfl⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨lp,hM,_⟩ ⟨⟨Tt,ev,hHT,fr,_,H',hH',hT,hE,nt⟩,hn'⟩ _
    subst ev
    exact hres L Tt H' M' G' lp hHT (fun x hx => by rw [fr x hx,hM]) hH' hT hE nt hn'

#print axioms aqgd_decCall_htabNew_g

/-- Exit facts of `lst_new(E, Cp)` from heap pointer `H` at memory `M1`. -/
def LNew (E Cp H : BitVec 64) (M1 : Mem) (X H' : BitVec 64) (M' : Mem) (G' : GA) : Prop :=
  H.toNat ≤ X.toNat ∧ (∃ Pp : BitVec 64, X.toNat + 24 ≤ Pp.toNat ∧ LHd X Pp 0#64 Cp M' ∧
    Pp.toNat + (E * Cp).toNat ≤ H'.toNat) ∧ HeapIs G' H' ∧ H'.toNat ≤ 33806089496 ∧
    ∀ x, x.toNat < H.toNat → M' x = M1 x

/-- The actual `var 1 name = lst_new(E, Cp)`. -/
theorem aqgd_decCall_lstNew_g {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (E Cp : BitVec 64)
    {cont : ProgHOL 64} (H Nj : BitVec 64) (M1 : Mem) (G1 : GA) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hw : w.toNat < H.toNat)
    (hres : ∀ (L : GA) (X H' : BitVec 64) (M' : Mem) (G' : GA), LP L → LNew E Cp H M1 X H' M' G' →
      G'.lookup (ofString "journal_n") = some (.val (.word Nj)) → Pc (L.update (name,.val (.word X))) M' G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "lst_new") [.const E,.const Cp] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "cap",Cp),(ofString "esz",E)] L ∧ M = M0' ∧ G = G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (LNPost E Cp H M0' G0' v M' G' ∧ ScrIs Sc G') ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_lstNew_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
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
  · intro F s values callee rs _ G hG ⟨_,_,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact] at ev1 ev2; subst ev1 ev2
    have e := callee_eq originalRuntimeCode_lstNew_lookup lookup
    refine ⟨⟨fun p hp => ?_,rfl,rfl⟩,by rw [hG1]; exact hn1⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨lp,hM,_⟩ ⟨⟨⟨⟨X,Pp,ev,hX,hXP,hd,H',hH',hP',hE⟩,fr,_⟩,_⟩,hn'⟩ _
    subst ev
    exact hres L X H' M' G' lp ⟨hX,⟨Pp,hXP,hd,hP'⟩,hH',hE,fun x hx => by rw [fr x hx,hM]⟩ hn'

#print axioms aqgd_decCall_lstNew_g

/-- The actual `name = lst_new(E, Cp)` (assigning call). -/
theorem aqgd_callAssign_lstNew_g {LP : GA → Prop} (name : MlS) (E Cp : BitVec 64) (H Nj : BitVec 64) (M1 : Mem)
    (G1 : GA) (hH1 : HeapIs G1 H) (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (hw : w.toNat < H.toNat) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => ∃ (L0 : GA) (X H' : BitVec 64), L = L0.update (name,.val (.word X)) ∧ LP L0 ∧
        LNew E Cp H M1 X H' M G ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) RR
      (.call (some (some (.local,name),none)) (ofString "lst_new") [.const E,.const Cp]) := by
  refine aqgd_callAssignF (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "cap",Cp),(ofString "esz",E)] L ∧ M = M0' ∧ G = G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (LNPost E Cp H M0' G0' v M' G' ∧ ScrIs Sc G') ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    _ _ _ _ _ _ originalRuntimeCode_lstNew_lookup (by simp) (fun h => h) ?_ ?_ ?_
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
  · intro F s values callee rs _ G hG ⟨_,_,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact] at ev1 ev2; subst ev1 ev2
    have e := callee_eq originalRuntimeCode_lstNew_lookup lookup
    refine ⟨⟨fun p hp => ?_,rfl,rfl⟩,by rw [hG1]; exact hn1⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨lp,hM,_⟩ ⟨⟨⟨⟨X,Pp,ev,hX,hXP,hd,H',hH',hP',hE⟩,fr,_⟩,_⟩,hn'⟩
    subst ev
    exact ⟨L,X,H',rfl,lp,⟨hX,⟨Pp,hXP,hd,hP'⟩,hH',hE,fun x hx => by rw [fr x hx,hM]⟩,hn'⟩

#print axioms aqgd_callAssign_lstNew_g
end gc
end InitECandidate.Runtime
