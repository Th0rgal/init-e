import InitECandidate.Runtime.PtSufDOGD
import InitECandidate.Runtime.PtSufBO2GD
/-!
The `lst_push` / `lst_new` call statements of the `process_transaction` suffix re-derived over the arena with the
`bal_*` globals pinned (`JWB`); their installed bodies pass the `bal_*` keep check (`BalKeep2`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem goodBal2_lstPush : goodBal2 (ofString "lst_push") = true := goodBal2_of_extra (by decide)

section ls2
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Hb Nj : BitVec 64} {M0 : Mem} {BA IA IS KB Ixb : BitVec 64}

/-- `name = lst_push(lds(bo + k), E)` on the block list `Lh = M0 (bo + k)` (count `Nc`); the other memory facts `R`
are framed by the header words and the words at or above the heap pointer. -/
theorem aqgd_decCall_lstPush_pbB (bk : BalKeep2) {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} {Wb : BitVec 64 → Prop}
    {R : Mem → GA → Prop} (name : MlS) (k E Lh Nc : BitVec 64)
    {cont : ProgHOL 64} (hWb : ∀ x, Wb x → BW n c Out Excl w x)
    (hOut : Out w) (hBk : Out (Bo + k) ∧ ¬ Excl (Bo + k) ∧ M0 (Bo + k) = .word Lh)
    (hE1 : 1 ≤ E.toNat) (hup : ∀ L v, LP L → LP' (L.update (name,v)))
    (hR : ∀ (M M' : Mem) (G G' : GA) (H H' : BitVec 64), R M G → HeapIs G H → Hb.toNat ≤ H.toNat → HeapIs G' H' →
      H.toNat ≤ H'.toNat →
      (∀ x, x.toNat < H.toNat → ¬ HdW Lh x → M' x = M x) → R M' G')
    (hcont : ∀ S : BitVec 64, AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => ((LP' L ∧ L.lookup name = some (.val (.word S))) ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        (BL Wb Hb Lh E M G ∧ M (Lh + 8#64) = .word (Nc + 1#64) ∧ Nc.toNat + 1 < 2 ^ 64) ∧
        SlotOK Wb Hb Lh S E G ∧ R M G) Q RR cont)
    (hres : ∀ L M G L' M' G', (LP L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
      (BL Wb Hb Lh E M G ∧ M (Lh + 8#64) = .word Nc) ∧ R M G →
      Q L' M' G' → Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LP L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧ (BL Wb Hb Lh E M G ∧ M (Lh + 8#64) = .word Nc) ∧
        R M G) Q2 RR
      (.decCall name .one (ofString "lst_push") [.load .one (.op .add [.var .global (ofString "bo"),.const k]),.const E]
        cont) := by
  refine aqgd_decCallSpecS (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M0' ∧ G = G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ((∃ P N Cp : BitVec 64, LHd Lh P N Cp M0' ∧ LPPost Lh E P N Cp (hpOf G0') M0' G0' v M' G') ∧ ScrIs Sc G') ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := fun L M G => ∃ S : BitVec 64, (((LP' L ∧ L.lookup name = some (.val (.word S))) ∧
      PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
      (BL Wb Hb Lh E M G ∧ M (Lh + 8#64) = .word (Nc + 1#64) ∧ Nc.toNat + 1 < 2 ^ 64) ∧
      SlotOK Wb Hb Lh S E G ∧ R M G) ∧ True)
    (Qc := Q) _ _ _ _ _ _ _ originalRuntimeCode_lstPush_lookup
    (fun values callee rs h => callee_entry_sl _ values _ _ _ originalRuntimeCode_lstPush_lookup (by simp) _ callee rs h)
    ?_ ?_ (fun h => h.elim) ?_ (aqgd_exE (fun S => aqgd_pureE (fun _ => hcont S))) hres
  · intro L0 M0' G0' ⟨⟨_,pb⟩,⟨⟨hW,hLb,P,N,Cp,H1,hd,hH1,hNC,hC0,hbuf,_⟩,_⟩,_⟩
    obtain ⟨⟨H,hH,hbH⟩,reg,hn,_⟩ := pb
    have e1 := heapIs_unique hH hH1
    subst e1
    rw [hpOf_eq hH]
    have hwH := regT_out_lt reg hOut
    have hwh : ¬ HdW Lh w := fun h => (hWb w (hW w h)).2.2.2 rfl
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G0' ∧ H.toNat ≤ 33806089496)
      (fun _ _ g aw ⟨⟨_,_,hg⟩,_⟩ => by subst hg; exact ⟨aw.1.2,(jws_heap_facts aw.1.1.1.1 hH).2.1⟩) ?_
    intro ⟨hsc,hHE⟩
    have hsz : E.toNat * Cp.toNat * 2 < 2 ^ 64 := by omega
    refine aqgd_conseq (P := fun L M G => (((LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M0' ∧
        HeapIs G H) ∧ G = G0') ∧ ScrIs Sc G) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) ?_
      (fun L M G h => by obtain ⟨⟨lk,hM,hG⟩,jn⟩ := h; subst hG; exact ⟨⟨⟨⟨lk,hM,hH⟩,rfl⟩,hsc⟩,jn⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_liftB bk (keepsAll_of_installed bk originalRuntimeCode_lstPush_lookup goodBal2_lstPush) <|
      aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_lstPush_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_lstPush_lookup (by decide))
      (P := fun L M G => ((LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M0' ∧ HeapIs G H) ∧ G = G0') ∧
        ScrIs Sc G) (Nj := Nj)
      (aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_lstPush_lookup (by decide))
        (lstPush_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
          (Nj := Nj) (w := w) Lh E P N Cp H M0' G0' (by omega) (by omega) hwh hd hNC hC0 hE1 (by omega) hsz))
        (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)))
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) ?_
    intro v M' G' ⟨⟨post,sc⟩,hn'⟩
    exact ⟨⟨⟨P,N,Cp,hd,post⟩,sc⟩,hn'⟩
  · intro F s values callee rs aw G hG ⟨⟨_,pb⟩,_,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    have e1 := ev_load_goff s _ Bo k v1 aw.1.1.1.2 ev1
    rw [pb.2.2.2 _ hBk.1 hBk.2.1,hBk.2.2] at e1
    subst e1
    simp [EV,evalHOLExact] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_lstPush_lookup lookup
    refine ⟨⟨fun p hp => ?_,rfl,rfl⟩,pb.2.2.1⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨⟨lp,pb⟩,⟨⟨hW,hLb,P0',N0,Cp0,H0',hd0,hH0,_,_,hbuf0,alt0⟩,hNc⟩,r⟩
      ⟨⟨⟨P,N,Cp,hd,post⟩,_⟩,hn'⟩ _
    obtain ⟨H,hH,hbH⟩ := pb.1
    have eH := heapIs_unique hH hH0
    subst eH
    rw [hpOf_eq hH] at post
    obtain ⟨fr,_,Pn,Cn,Hc,ev,hd',hHc,le,lt,hbuf',alt⟩ := post
    subst ev
    have eP := word_inj hd.1 hd0.1
    have eC := word_inj hd.2.2 hd0.2.2
    have eN := word_inj hd.2.1 hNc
    subst eP eC eN
    have hHc64 : Hc.toNat < 2 ^ 64 := Hc.isLt
    have sa := slot_arith (E := E.toNat) lt
    have eNE : (N * E).toNat = N.toNat * E.toNat := mul_nat (by omega)
    have eS : (Pn + N * E).toNat = Pn.toNat + N.toNat * E.toNat := by
      rw [BitVec.toNat_add,eNE]; exact Nat.mod_eq_of_lt (by omega)
    have eN1 : (N + 1#64).toNat = N.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    refine ⟨Pn + N * E,⟨⟨⟨hup L _ lp,lookup_update_eq' _ _ _⟩,pb_glob (pb_wr (HdW Lh) pb
      (fun x hx => let b := hWb x (hW x hx); ⟨b.1,b.2.1,b.2.2.1⟩) (fun x hx hn => fr x (by omega) hn))
        ⟨Hc,hHc,by omega⟩ hn'⟩,
      ⟨⟨hW,hLb,Pn,N + 1#64,Cn,Hc,hd',hHc,by omega,by omega,hbuf',?_⟩,hd'.2.1,by omega⟩,⟨by omega,?_⟩,
      hR M M' G G' H Hc r hH hbH hHc le fr⟩,trivial⟩
    · rcases alt with ⟨rfl,rfl⟩ | ⟨hp,_⟩
      · exact alt0
      · exact Or.inr (by omega)
    · rcases alt with ⟨rfl,rfl⟩ | ⟨hp,_⟩
      · rcases alt0 with inW | hp
        · exact Or.inl (fun x lo hi => inW x (by omega) (by omega))
        · exact Or.inr ⟨Hc,hHc,by omega,by omega⟩
      · exact Or.inr ⟨Hc,hHc,by omega,by omega⟩

#print axioms aqgd_decCall_lstPush_pbB
end ls2

section ln2
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Hb Nj : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}
  {BA IA IS KB Ixb : BitVec 64}

/-- `name = lst_new(E, x)` (`x = Cp`) in the suffix state: a fresh header `X ≥ Hb` with buffer `[Pp, Pp + E·Cp)`,
`X + 24 ≤ Pp`; side facts `R` framed below the heap pointer at the call. -/
theorem aqgd_decCall_lstNewC_pbB (bk : BalKeep2) {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} {R : Mem → GA → Prop}
    (name xname : MlS) (E Cp : BitVec 64) {cont : ProgHOL 64} (hOut : Out w)
    (hx : ∀ L, LP L → L.lookup xname = some (.val (.word Cp)))
    (hup : ∀ L v, LP L → LP' (L.update (name,v)))
    (hR : ∀ (M M' : Mem) (G G' : GA) (H H' : BitVec 64), R M G → HeapIs G H → Hb.toNat ≤ H.toNat → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x, x.toNat < H.toNat → M' x = M x) → R M' G')
    (hcont : ∀ X Pp : BitVec 64, AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (((LP' L ∧ L.lookup name = some (.val (.word X))) ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        R M G) ∧ (Hb.toNat ≤ X.toNat ∧ X.toNat + 24 ≤ Pp.toNat ∧ LHd X Pp 0#64 Cp M ∧
          ∃ H : BitVec 64, HeapIs G H ∧ Pp.toNat + (E * Cp).toNat ≤ H.toNat)) Q RR cont)
    (hres : ∀ L M G L' M' G', (LP L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧ R M G →
      Q L' M' G' → Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LP L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧ R M G) Q2 RR
      (.decCall name .one (ofString "lst_new") [.const E,.var .local xname] cont) := by
  refine aqgd_decCallSpecS (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "cap",Cp),(ofString "esz",E)] L ∧ M = M0' ∧ G = G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (LNPost E Cp (hpOf G0') M0' G0' v M' G' ∧ ScrIs Sc G') ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := fun L M G => ∃ X Pp : BitVec 64, ((((LP' L ∧ L.lookup name = some (.val (.word X))) ∧
      PB n c T Out ko D B Excl Hb Nj M0 M G) ∧ R M G) ∧ (Hb.toNat ≤ X.toNat ∧ X.toNat + 24 ≤ Pp.toNat ∧
        LHd X Pp 0#64 Cp M ∧ ∃ H : BitVec 64, HeapIs G H ∧ Pp.toNat + (E * Cp).toNat ≤ H.toNat)) ∧ True)
    (Qc := Q) _ _ _ _ _ _ _ originalRuntimeCode_lstNew_lookup
    (fun values callee rs h => callee_entry_sl _ values _ _ _ originalRuntimeCode_lstNew_lookup (by simp) _ callee rs h)
    ?_ ?_ (fun h => h.elim) ?_ (aqgd_exE (fun X => aqgd_exE (fun Pp => aqgd_pureE (fun _ => hcont X Pp)))) hres
  · intro L0 M0' G0' ⟨⟨_,⟨H,hH,hbH⟩,reg,hn,_⟩,_⟩
    rw [hpOf_eq hH]
    have hwH := regT_out_lt reg hOut
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G0') (fun _ _ g aw ⟨⟨_,_,hg⟩,_⟩ => by subst hg; exact aw.1.2) ?_
    intro hsc
    refine aqgd_conseq (P := fun L M G => (((LK [(ofString "cap",Cp),(ofString "esz",E)] L ∧ M = M0' ∧
        HeapIs G H) ∧ G = G0') ∧ ScrIs Sc G) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) ?_
      (fun L M G h => by obtain ⟨⟨lk,hM,hG⟩,jn⟩ := h; subst hG; exact ⟨⟨⟨⟨lk,hM,hH⟩,rfl⟩,hsc⟩,jn⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    exact aqgd_liftB bk (keepsAll_of_installed bk originalRuntimeCode_lstNew_lookup goodBal2_lstNew) <|
      aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_lstNew_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_lstNew_lookup (by decide))
      (P := fun L M G => ((LK [(ofString "cap",Cp),(ofString "esz",E)] L ∧ M = M0' ∧ HeapIs G H) ∧ G = G0') ∧
        ScrIs Sc G) (Nj := Nj)
      (aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_lstNew_lookup (by decide))
        (lstNewC_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
          (Nj := Nj) (w := w) E Cp H (by omega) M0' G0'))
        (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)))
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs aw G hG ⟨⟨lp,pb⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact] at ev1; subst ev1
    simp [EV,evalHOLExact,hx _ lp] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_lstNew_lookup lookup
    refine ⟨⟨fun p hp => ?_,rfl,rfl⟩,pb.2.2.1⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨⟨lp,pb⟩,r⟩ ⟨⟨⟨⟨X,Pp,ev,hX,hXP,hd,H',hH',hP',_⟩,fr,_⟩,_⟩,hn'⟩ _
    obtain ⟨H,hH,hbH⟩ := pb.1
    rw [hpOf_eq hH] at hX fr
    subst ev
    have le : H.toNat ≤ H'.toNat := by
      have : (E * Cp).toNat ≥ 0 := Nat.zero_le _
      omega
    refine ⟨X,Pp,⟨⟨⟨⟨hup L _ lp,lookup_update_eq' _ _ _⟩,pb_glob (pb_wr (fun _ => False) pb (fun _ h => h.elim)
      (fun x hx _ => fr x (by omega))) ⟨H',hH',by omega⟩ hn'⟩,hR M M' G G' H H' r hH hbH hH' le fr⟩,
      by omega,hXP,hd,H',hH',hP'⟩,trivial⟩

#print axioms aqgd_decCall_lstNewC_pbB
end ln2
end InitECandidate.Runtime
