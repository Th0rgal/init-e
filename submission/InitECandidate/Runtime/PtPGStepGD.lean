import InitECandidate.Runtime.PtPGGD
/-!
Final-phase (`PG`) steps of the `process_transaction` segment: word stores into `[Lo, Hg)` below the `aa` table,
constant allocations, and the actual `htab_set` on the fresh `aa` table (valid in `[Taa, Pa)`, `Pa ≤ Hg`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ps
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Hg Hb Nj : BitVec 64} {M0 : Mem}

theorem aqgd_call_htabSet_pg {LP : GA → Prop} (tn : MlS) (ek ev : ExpHOL 64)
    (Tt Pa : BitVec 64) (hLoA : Lo.toNat ≤ Tt.toNat) (hPa : Pa.toNat ≤ Hg.toNat) (hgb : Hg.toNat ≤ Hb.toNat)
    (hw : w.toNat < Lo.toNat) (hcLo : ∀ i, (c i).toNat < Lo.toNat) (hOutLo : ∀ x, Out x → x.toNat < Lo.toNat)
    (ht : ∀ L, LP L → L.lookup tn = some (.val (.word Tt))) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Tt Tt Pa M)
      (fun L M G => LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) RR
      (.call (some (none,none)) (ofString "htab_set") [.var .local tn,ek,ev]) := by
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ Kk V : BitVec 64, LK (irP0 Tt Kk V) L) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ (P Hc KL SD Cc N KS VS US OS OPS : BitVec 64) (b : Nat), HeapIs G0' Hc ∧ P.toNat ≤ Hc.toNat ∧
        P.toNat ≤ Hg.toNat ∧ Hb.toNat ≤ Hc.toNat ∧
        (HLay P Tt (Canon Tt Cc SD KS VS US OS OPS P) KL SD Cc N KS VS US OS OPS b ∧ Tt.toNat ≤ Tt.toNat ∧
          LayIn (fun x => Tt.toNat ≤ x.toNat ∧ x.toNat < P.toNat) Cc SD KS VS US OS OPS) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
          SetPost Tt (Canon Tt Cc SD KS VS US OS OPS Hc) M0' Cc SD KS VS US OS OPS Hc M' H')
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨⟨_,⟨Hc,hHc,leb⟩,_,hn0,_⟩,⟨KL,SD,Cc,N,KS,VS,US,OS,OPS,b,lay,hd,a,li⟩⟩
    have le : Pa.toNat ≤ Hc.toNat := by omega
    refine aqgd_of_arenaFact (Φ := P0.toNat ≤ Hc.toNat) (fun _ _ g aw ⟨_,_,hg⟩ => by
      subst hg; exact (jws_heap_facts aw.1.1.1 hHc).1) ?_
    intro hP0
    have hwF : ¬ Foot Hc Tt (Canon Tt Cc SD KS VS US OS OPS Hc) w := fun hc => by
      have := canon_ge a (fun y hy => let ⟨h1,h2⟩ := li y hy; ⟨h1,by omega⟩) (by have := lay.hdrP; omega) hc
      omega
    refine aqgd_conseq (P := fun L M G => ∃ Kk V : BitVec 64, LK (irP0 Tt Kk V) L ∧ M = M0' ∧ G = G0') ?_
      (fun _ _ _ ⟨⟨Kk,V,lk⟩,hm,hg⟩ => ⟨Kk,V,lk,hm,hg⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_exE (fun Kk => aqgd_exE (fun V => ?_))
    refine aqgd_conseq (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J)
      (C := C) (N := Nj) originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (aqmh_lower hP0 (set_aqmh (SP0 := SP0) (FM := FM) (G0 := G0) (P0 := Hc) Tt Kk V _ KL SD Cc N KS VS US OS OPS b
        (hlay_canon lay le) M0' hwF Hc (le_refl _)))))
      (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_hashSet_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_hashSet_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_hashSet_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨lk,hM,hG⟩
      subst hM hG
      exact ⟨hn0,Hc,hHc,⟨lk,hd,rfl,rfl⟩,rfl⟩
    · intro v M' G' ⟨hn',H',hH',post⟩
      exact ⟨Pa,Hc,KL,SD,Cc,N,KS,VS,US,OS,OPS,b,hHc,le,hPa,leb,⟨lay,a,li⟩,hn',H',hH',post⟩
  · intro F s values callee rs _ H hG ⟨⟨lp,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,_,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,ht _ lp] at ev1; subst ev1
    obtain ⟨_,Kk,V,_,rfl,rfl⟩ := entry3_words originalRuntimeCode_hashSet_lookup lookup
    have e := callee_eq originalRuntimeCode_hashSet_lookup lookup
    refine ⟨⟨Kk,V,fun p hp => ?_⟩,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨⟨lp,pg⟩,_⟩ ⟨P,Hc,KL,SD,Cc,N,KS,VS,US,OS,OPS,b,hHc,le,hPg,hbc,⟨lay,a,li⟩,hn',H',hH',post⟩
    have hdrP := lay.hdrP
    have leH := post.1
    have fo := set_frame_out a li hdrP post
    refine ⟨lp,pg_glob (pg_in (fun x => Tt.toNat ≤ x.toNat ∧ x.toNat < P.toNat) pg (fun x hx => ?_)
      (fun x hx hs => fo x hs (by omega))) ⟨H',hH',by omega⟩ hn'⟩
    refine ⟨⟨by omega,by omega⟩,fun i e => ?_,fun ho => ?_⟩
    · have := hcLo i; rw [← e] at this; omega
    · have := hOutLo x ho; omega

#print axioms aqgd_call_htabSet_pg

/-- A word store into `[Lo, Taa)` keeps `PG` and the `aa` table. -/
theorem aqgd_stw_pg {A : GA → Prop} {Vn : MlS → Prop} {LP : GA → Prop} (Taa Pa : BitVec 64)
    (hw : w.toNat < Lo.toNat) (hcLo : ∀ i, (c i).toNat < Lo.toNat) (hOutLo : ∀ x, Out x → x.toNat < Lo.toNat)
    (hTg : Taa.toNat ≤ Hg.toNat) (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ Lo.toNat ≤ a.toNat ∧ a.toNat < Taa.toNat)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals → EV s v = some x →
      ∃ y : BitVec 64, x = .val (.word y)) :
    AQGD D B A w Vn (fun L M G => (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M)
      (fun L M G => (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M) RR (.store d v) := by
  refine aqgd_storeD _ _ (fun s H _ _ hG ⟨⟨lp,pg⟩,tv⟩ _ => ?_) (fun s x _ _ _ _ pre _ ev => hv s x pre.1.1 ev)
  unfold GIs at hG; subst hG
  obtain ⟨a,ha,lo,hi⟩ := hd s lp
  refine ⟨a,ha,fun e => by subst e; omega,fun y _ => ⟨⟨lp,pg_in (fun x => x = a) pg ?_ ?_⟩,tabV_frame tv ?_⟩⟩
  · intro x hx; subst hx
    refine ⟨⟨lo,by omega⟩,fun i e => ?_,fun ho => ?_⟩
    · have := hcLo i; rw [← e] at this; omega
    · have := hOutLo x ho; omega
  · intro x _ hx; simp [hx]
  · intro x hx _
    have : x ≠ a := fun e => by subst e; omega
    simp [this]

#print axioms aqgd_stw_pg

/-- `name = alloc(N)` (constant size) in the final phase: the block `X ≥ Hb`, `X + N ≤ HEAP_END`. -/
theorem aqgd_decCall_allocC_pg {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name : MlS) (Nn Taa Pa : BitVec 64)
    {cont : ProgHOL 64} (hup : ∀ L v, LP L → LP' (L.update (name,v)))
    (hcont : ∀ X : BitVec 64, Hb.toNat ≤ X.toNat → X.toNat + Nn.toNat ≤ 33806089496 → X.toNat % 8 = 0 →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => ((LP' L ∧ L.lookup name = some (.val (.word X))) ∧
          PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M) Q RR cont)
    (hres : ∀ L M G L' M' G', (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M →
      Q L' M' G' → Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M) Q2 RR
      (.decCall name .one (ofString "alloc") [.const Nn] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ X : BitVec 64, HeapIs G0' X ∧ (v = .val (.word X) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
        X.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ X.toNat % 8 = 0 ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := fun L M G => ∃ X : BitVec 64, (((LP' L ∧ L.lookup name = some (.val (.word X))) ∧
      PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M) ∧
        (Hb.toNat ≤ X.toNat ∧ X.toNat + Nn.toNat ≤ 33806089496 ∧ X.toNat % 8 = 0)) (Qc := Q)
    _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_
    (aqgd_exE (fun X => aqgd_pureE (fun ⟨a,b,c⟩ => hcont X a b c))) hres
  · intro L0 M0' G0' ⟨⟨_,⟨Hc,hH,_⟩,_,hn,_⟩,_⟩
    refine aqgd_conseq (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J)
      (C := C) (N := Nj) originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) Nn Hc M0')))
      (keepsSkBuf_of_installed originalRuntimeCode_allocation_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_allocation_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_allocation_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_allocation_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hl,hM,hG⟩
      subst hM hG
      exact ⟨hn,Hc,hH,hl,rfl,rfl⟩
    · intro v M' G' ⟨hn',H',hH',eM,ev,_,_,c1,c2,_,al⟩
      exact ⟨Hc,hH,⟨ev,eM,H',hH',c1,c2⟩,al,hn'⟩
  · intro F s values callee rs _ H _ _ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨lp,pg⟩,tv⟩ ⟨X,hH,⟨ev,eM,H',hH',c1,c2⟩,al,hn'⟩ _
    subst ev eM
    obtain ⟨H1,hH1,le1⟩ := pg.1
    have e := heapIs_unique hH1 hH
    subst e
    exact ⟨H1,⟨⟨⟨hup L _ lp,lookup_update_eq' _ _ _⟩,pg_glob pg ⟨H',hH',by omega⟩ hn'⟩,tv⟩,le1,by omega,al⟩

#print axioms aqgd_decCall_allocC_pg

/-- A word store into `[Lo, Hg)` keeps `PG`. -/
theorem aqgd_stw_pg0 {A : GA → Prop} {Vn : MlS → Prop} {LP : GA → Prop}
    (hw : w.toNat < Lo.toNat) (hcLo : ∀ i, (c i).toNat < Lo.toNat) (hOutLo : ∀ x, Out x → x.toNat < Lo.toNat)
    (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ Lo.toNat ≤ a.toNat ∧ a.toNat < Hg.toNat)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals → EV s v = some x →
      ∃ y : BitVec 64, x = .val (.word y)) :
    AQGD D B A w Vn (fun L M G => LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G)
      (fun L M G => LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) RR (.store d v) := by
  refine aqgd_storeD _ _ (fun s H _ _ hG ⟨lp,pg⟩ _ => ?_) (fun s x _ _ _ _ pre _ ev => hv s x pre.1 ev)
  unfold GIs at hG; subst hG
  obtain ⟨a,ha,lo,hi⟩ := hd s lp
  refine ⟨a,ha,fun e => by subst e; omega,fun y _ => ⟨lp,pg_in (fun x => x = a) pg ?_ ?_⟩⟩
  · intro x hx; subst hx
    refine ⟨⟨lo,hi⟩,fun i e => ?_,fun ho => ?_⟩
    · have := hcLo i; rw [← e] at this; omega
    · have := hOutLo x ho; omega
  · intro x _ hx; simp [hx]

#print axioms aqgd_stw_pg0
end ps
end InitECandidate.Runtime
