import InitECandidate.Runtime.PtSegTeGD
/-!
`process_transaction` spine drops 41-48: `nal`, `hal = tx_has_access_list(tx)`, the decoded `nal` load,
`al_addrs = alloc((nal + 1) * 8)` (unchecked decoded size: only the returned pointer `Aa ≥ Lo` is used), the store of
the coinbase word, and the address loop `st al_addrs + (i + 1) * 8, ...`. The loop cursor is fenced: the invariant
`Aa + 8 i ≤ DF` holds at entry (`Aa ≤ HEAP_END ≤ DF`) and a successful store learns its address is in the domain,
hence below `DF`, before `i` advances; with `DF + 8 ≤ 2^62` no address wraps, so every store is at or above `Lo`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem lte_upd {Ix S Lo : BitVec 64} {L : GA} (h : LTe Ix S Lo L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "index" ≠ x) (h2 : ofString "sender" ≠ x) (h3 : ofString "te" ≠ x) :
    LTe Ix S Lo (L.update (x,v)) :=
  ⟨lk_update h.1 x v (by simp only [List.mem_cons,List.not_mem_nil,or_false]; rintro p (rfl | rfl) <;> assumption),
    fb_upd h.2 x v h3⟩

theorem lte_res {Ix S Lo : BitVec 64} {L : GA} (h : LTe Ix S Lo L) (x : MlS) (o : Option (ValueHOL 64))
    (h1 : ofString "index" ≠ x) (h2 : ofString "sender" ≠ x) (h3 : ofString "te" ≠ x) :
    LTe Ix S Lo (L.resVarEq (x,o)) :=
  ⟨lk_res h.1 x o (by simp only [List.mem_cons,List.not_mem_nil,or_false]; rintro p (rfl | rfl) <;> assumption),
    fb_res h.2 x o h3⟩

section al
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Nj : BitVec 64} {M0 : Mem}

/-- `name = alloc(e)` for any size expression, keeping `SI`: the new local is the entry heap pointer `Hb`, at or above
`Lo`, 8-aligned and at most `HEAP_END`. -/
theorem aqgd_decCall_allocE_si {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name : MlS) (e : ExpHOL 64)
    {cont : ProgHOL 64} (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, EV s e = some x →
      ∃ y : BitVec 64, x = .val (.word y))
    (hup : ∀ L (Hb : BitVec 64), LP L → Lo.toNat ≤ Hb.toNat → Hb.toNat ≤ 33806089496 → Hb.toNat % 8 = 0 →
      LP' (L.update (name,.val (.word Hb))))
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP' L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) Q2 RR
      (.decCall name .one (ofString "alloc") [e] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ Nn : BitVec 64, L.lookup (ofString "n") = some (.val (.word Nn))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ Hb : BitVec 64, HeapIs G0' Hb ∧ Hb.toNat % 8 = 0 ∧ Hb.toNat ≤ 33806089496 ∧
        (v = .val (.word Hb) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ Hb.toNat ≤ H'.toNat) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := fun L M G => LP' L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (Qc := Q)
    _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hcont hres
  · intro L0 M0' G0' ⟨_,⟨Hb,hH,_⟩,_,hn,_⟩
    refine aqgd_of_arenaFact (Φ := (P0.toNat ≤ Hb.toNat ∧ Hb.toNat ≤ 33806089496 ∧ Hb.toNat % 8 = 0) ∧ ScrIs Sc G0')
      (fun _ _ g aw ⟨_,_,hg⟩ => by subst hg; exact ⟨jws_heap_facts aw.1.1.1 hH,aw.2⟩) ?_
    intro ⟨⟨_,hcapH,hal⟩,hsc⟩
    refine aqgd_conseq (P := fun L M G => ∃ Nn : BitVec 64, (L.lookup (ofString "n") = some (.val (.word Nn)) ∧
        M = M0' ∧ G = G0'))
      ?_ (fun L M G ⟨⟨Nn,hN⟩,hM,hG⟩ => ⟨Nn,hN,hM,hG⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_exE (fun Nn => ?_)
    refine aqgd_conseq (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J)
      (C := C) (N := Nj) originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) Nn Hb M0')))
      (keepsSkBuf_of_installed originalRuntimeCode_allocation_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_allocation_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_allocation_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_allocation_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hl,hM,hG⟩
      subst hM hG
      exact ⟨hn,Hb,hH,hl,rfl,rfl⟩
    · intro v M' G' ⟨hn',H',hH',eM,ev,_,_,c1,_,_,_⟩
      exact ⟨Hb,hH,hal,hcapH,⟨ev,eM,H',hH',by omega⟩,hn'⟩
  · intro F s values callee rs _ H _ _ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    obtain ⟨y,rfl⟩ := he s x ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,si⟩ ⟨Hb,hH,hal,hcap,⟨ev,eM,H',hH',le'⟩,hn'⟩ _
    subst ev eM
    obtain ⟨H1,hH1,le1⟩ := si.1
    have e := heapIs_unique hH1 hH
    subst e
    exact ⟨hup L H1 lp le1 hcap hal,si_glob si ⟨H',hH',by omega⟩ hn'⟩

#print axioms aqgd_decCall_allocE_si

/-- `while` with a memory-carrying invariant and no break. -/
theorem aqgd_whileI {A : GA → Prop} {Vn : MlS → Prop} {I : GA → Mem → GA → Prop} (c : ExpHOL 64) {body : ProgHOL 64}
    (hb : AQGD D B A w Vn (fun L M G => I L M G ∧ True) I RR body) :
    AQGD D B A w Vn I I RR (.while c body) :=
  aqgd_conseq (aqgd_whileBreak (I := I) (C := fun _ _ _ => True) (Qb := fun _ _ _ => False) _
      (fun _ _ _ _ _ _ _ _ => trivial) (aqgb_of_aqgd hb))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h)

/-- Locals after `al_addrs = alloc(..)`: `LTe` and the fresh pointer `Aa ≥ Lo`. -/
def LAa (Ix S Lo : BitVec 64) (L : GA) : Prop :=
  LTe Ix S Lo L ∧ ∃ Aa : BitVec 64, L.lookup (ofString "al_addrs") = some (.val (.word Aa)) ∧
    Lo.toNat ≤ Aa.toNat ∧ Aa.toNat ≤ 33806089496

/-- The address-loop invariant: the cursor base `Aa ≥ Lo` and index `I` with `Aa + 8 I ≤ DF`. -/
def LAI (Ix S Lo : BitVec 64) (DF : Nat) (L : GA) : Prop :=
  LTe Ix S Lo L ∧ ∃ Aa I : BitVec 64, L.lookup (ofString "al_addrs") = some (.val (.word Aa)) ∧
    L.lookup (ofString "i") = some (.val (.word I)) ∧ Lo.toNat ≤ Aa.toNat ∧ Aa.toNat + 8 * I.toNat ≤ DF

/-- The address-loop invariant after the store of index `I + 1`. -/
def LAI1 (Ix S Lo : BitVec 64) (DF : Nat) (L : GA) : Prop :=
  LTe Ix S Lo L ∧ ∃ Aa I : BitVec 64, L.lookup (ofString "al_addrs") = some (.val (.word Aa)) ∧
    L.lookup (ofString "i") = some (.val (.word I)) ∧ Lo.toNat ≤ Aa.toNat ∧ Aa.toNat + 8 * (I.toNat + 1) ≤ DF

theorem laa_upd {Ix S Lo : BitVec 64} {L : GA} (h : LAa Ix S Lo L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "index" ≠ x) (h2 : ofString "sender" ≠ x) (h3 : ofString "te" ≠ x) (h4 : ofString "al_addrs" ≠ x) :
    LAa Ix S Lo (L.update (x,v)) :=
  let ⟨lt,Aa,hA,a,b⟩ := h; ⟨lte_upd lt x v h1 h2 h3,Aa,by rw [lookup_update_ne' _ _ h4]; exact hA,a,b⟩

theorem lai_upd {Ix S Lo : BitVec 64} {DF : Nat} {L : GA} (h : LAI Ix S Lo DF L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "index" ≠ x) (h2 : ofString "sender" ≠ x) (h3 : ofString "te" ≠ x) (h4 : ofString "al_addrs" ≠ x)
    (h5 : ofString "i" ≠ x) : LAI Ix S Lo DF (L.update (x,v)) :=
  let ⟨lt,Aa,I,hA,hI,a,b⟩ := h
  ⟨lte_upd lt x v h1 h2 h3,Aa,I,by rw [lookup_update_ne' _ _ h4]; exact hA,by rw [lookup_update_ne' _ _ h5]; exact hI,a,b⟩

theorem lai_res {Ix S Lo : BitVec 64} {DF : Nat} {L : GA} (h : LAI Ix S Lo DF L) (x : MlS) (o : Option (ValueHOL 64))
    (h1 : ofString "index" ≠ x) (h2 : ofString "sender" ≠ x) (h3 : ofString "te" ≠ x) (h4 : ofString "al_addrs" ≠ x)
    (h5 : ofString "i" ≠ x) : LAI Ix S Lo DF (L.resVarEq (x,o)) :=
  let ⟨lt,Aa,I,hA,hI,a,b⟩ := h
  ⟨lte_res lt x o h1 h2 h3,Aa,I,by rw [resVarEq_lookup_ne' _ _ _ _ h4]; exact hA,
    by rw [resVarEq_lookup_ne' _ _ _ _ h5]; exact hI,a,b⟩

theorem lai1_upd {Ix S Lo : BitVec 64} {DF : Nat} {L : GA} (h : LAI1 Ix S Lo DF L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "index" ≠ x) (h2 : ofString "sender" ≠ x) (h3 : ofString "te" ≠ x) (h4 : ofString "al_addrs" ≠ x)
    (h5 : ofString "i" ≠ x) : LAI1 Ix S Lo DF (L.update (x,v)) :=
  let ⟨lt,Aa,I,hA,hI,a,b⟩ := h
  ⟨lte_upd lt x v h1 h2 h3,Aa,I,by rw [lookup_update_ne' _ _ h4]; exact hA,by rw [lookup_update_ne' _ _ h5]; exact hI,a,b⟩

/-- The body of the address loop: `acc`, the fenced store at `al_addrs + (i + 1) * 8`, `nkeys`, `i = i + 1`. -/
theorem alLoopBody (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hw : w.toNat < Lo.toNat) (Ix S : BitVec 64) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LAI Ix S Lo DF L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ True)
      (fun L M G => LAI Ix S Lo DF L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) RR
      (.dec (ofString "acc") .one (.op .add [(.load .one (.op .add [(.var .local (ofString "tx")),(.const 208)])),(.panop .mul [(.var .local (ofString "i")),(.const 24)])])
        (.seq (.store (.op .add [(.var .local (ofString "al_addrs")),(.panop .mul [(.op .add [(.var .local (ofString "i")),(.const 1)]),(.const 8)])]) (.load .one (.op .add [(.var .local (ofString "acc")),(.const 0)])))
        (.seq (.assign .local (ofString "nkeys") (.op .add [(.var .local (ofString "nkeys")),(.load .one (.op .add [(.var .local (ofString "acc")),(.const 16)]))]))
          (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)]))))) := by
  refine aqgd_dec (Pb := fun L M G => LAI Ix S Lo DF L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    (Qb := fun L M G => LAI Ix S Lo DF L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ pre _ _ _ => ⟨lai_upd pre.1.1 _ v (by decide) (by decide) (by decide) (by decide) (by decide),
      pre.1.2⟩) ?_
    (fun _ _ _ _ _ _ _ q => ⟨lai_res q.1 _ _ (by decide) (by decide) (by decide) (by decide) (by decide),q.2⟩)
  refine aqgd_seq (aqgd_store_si (LP := LAI Ix S Lo DF) (LQ := LAI1 Ix S Lo DF) hw _ _ ?_
    (fun s x _ ev => ev_load_one_word s _ x ev)) ?_
  · intro F s _ ⟨lt,Aa,I,hA,hI,lo,hb⟩
    have e : (Aa + (I + 1#64) * 8#64).toNat = Aa.toNat + 8 * (I.toNat + 1) := by
      simp [BitVec.toNat_add,BitVec.toNat_mul]; omega
    refine ⟨Aa + (I + 1#64) * 8#64,?_,by omega,fun hD => ⟨lt,Aa,I,hA,hI,lo,?_⟩⟩
    · simp [EV,evalHOLExact,evalListHOLExact,hA,hI,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
    · have := hF _ hD; omega
  refine aqgd_seq (aqgd_assignLocal (Q := fun L M G => LAI1 Ix S Lo DF L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    _ _ (fun s v _ _ pre _ _ => ⟨lai1_upd pre.1 _ v (by decide) (by decide) (by decide) (by decide) (by decide),pre.2⟩)) ?_
  refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨lt,Aa,I,hA,hI,lo,hb⟩,si⟩ _ ev => ?_)
  simp [EV,evalHOLExact,evalListHOLExact,hI,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
  subst ev
  have e : (I + 1#64).toNat = I.toNat + 1 := by simp [BitVec.toNat_add]; omega
  exact ⟨⟨lte_upd lt _ _ (by decide) (by decide) (by decide),Aa,I + 1#64,
    by rw [lookup_update_ne' _ _ (by decide)]; exact hA,lookup_update_eq' _ _ _,lo,by rw [e]; omega⟩,si⟩

#print axioms alLoopBody

/-- Spine drops 41-48 of the actual `process_transaction`. -/
theorem ptSegAl {QM : Mem → GA → Prop} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (hw : w.toNat < Lo.toNat) (Ix S : BitVec 64) {cont : ProgHOL 64}
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (fun _ M G => QM M G) RR
      (.dec (ofString "nal") .one (.const 0)
      (.decCall (ofString "hal") .one (ofString "tx_has_access_list") [(.var .local (ofString "tx"))]
      (.seq (.ite (.cmp .notEqual (.var .local (ofString "hal")) (.const 0)) (.assign .local (ofString "nal") (.load .one (.op .add [(.var .local (ofString "tx")),(.const 216)]))) .skip)
      (.decCall (ofString "al_addrs") .one (ofString "alloc") [(.panop .mul [(.op .add [(.var .local (ofString "nal")),(.const 1)]),(.const 8)])]
      (.seq (.store (.var .local (ofString "al_addrs")) (.load .one (.op .add [(.var .global (ofString "be")),(.const 32)])))
      (.dec (ofString "nkeys") .one (.const 0)
      (.dec (ofString "i") .one (.const 0)
      (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) (.dec (ofString "acc") .one (.op .add [(.load .one (.op .add [(.var .local (ofString "tx")),(.const 208)])),(.panop .mul [(.var .local (ofString "i")),(.const 24)])]) (.seq (.store (.op .add [(.var .local (ofString "al_addrs")),(.panop .mul [(.op .add [(.var .local (ofString "i")),(.const 1)]),(.const 8)])]) (.load .one (.op .add [(.var .local (ofString "acc")),(.const 0)]))) (.seq (.assign .local (ofString "nkeys") (.op .add [(.var .local (ofString "nkeys")),(.load .one (.op .add [(.var .local (ofString "acc")),(.const 16)]))])) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)]))))))
        cont)))))))) := by
  have hD : DF + 8 ≤ 2 ^ 64 := by omega
  refine aqgd_dec (Pb := fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    (Qb := fun _ M G => QM M G) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ pre _ _ _ => ⟨lte_upd pre.1 _ v (by decide) (by decide) (by decide),pre.2⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_decCall_mf (I' := fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    _ _ _ _ _ _ _ originalRuntimeCode_txHasAccessList_lookup (by simp)
    (memoryFrame_of_good originalRuntimeCode_txHasAccessList_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_tx_has_access_list) (by body_check Guest.guestFn_tx_has_access_list)
    (fun L M G v pre => ⟨lte_upd pre.1 _ v (by decide) (by decide) (by decide),pre.2⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq (aqgd_iteT _ (aqgd_assignLocal _ _ (fun s v _ _ pre _ _ =>
    ⟨lte_upd pre.1 _ v (by decide) (by decide) (by decide),pre.2⟩)) aqgd_skip) ?_
  refine aqgd_decCall_allocE_si (LP' := LAa Ix S Lo) _ _ (fun s x ev => ev_panop_word s _ _ x ev)
    (fun L Hb lp le hi _ => ⟨lte_upd lp _ _ (by decide) (by decide) (by decide),Hb,lookup_update_eq' _ _ _,le,hi⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq (aqgd_storeAny_si (LP := LAa Ix S Lo) (LQ := LAa Ix S Lo) hF hD hw _ _
    (fun s _ lp => let ⟨_,Aa,hA,lo,_⟩ := lp; ⟨Aa,by simp [EV,evalHOLExact,hA],lo,lp⟩)) ?_
  refine aqgd_dec (Pb := fun L M G => LAa Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    (Qb := fun _ M G => QM M G) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ pre _ _ _ => ⟨laa_upd pre.1 _ v (by decide) (by decide) (by decide) (by decide),pre.2⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_dec (Pb := fun L M G => LAI Ix S Lo DF L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    (Qb := fun _ M G => QM M G) _ _ _ (fun h => h.elim) (fun s v _ _ _ pre _ ev _ => ?_) ?_
    (fun _ _ _ _ _ _ _ h => h)
  · simp [EV,evalHOLExact] at ev
    subst ev
    obtain ⟨⟨lt,Aa,hA,lo,hi⟩,si⟩ := pre
    exact ⟨⟨lte_upd lt _ _ (by decide) (by decide) (by decide),Aa,0#64,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hA,lookup_update_eq' _ _ _,lo,by simp; omega⟩,si⟩
  refine aqgd_seq (aqgd_whileI _ (alLoopBody hF hDF hw Ix S)) ?_
  exact aqgd_conseq hcont (fun _ _ _ h => ⟨h.1.1,h.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSegAl
end al
end InitECandidate.Runtime
