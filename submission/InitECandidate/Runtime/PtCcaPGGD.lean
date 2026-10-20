import InitECandidate.Runtime.PtCcaGD
/-!
`compute_contract_address(sender, nonce - 1, ct)` at the final-phase (`PG`) call site: the whole-memory frame of
`cca_wn` at the current heap pointer `Hc` (per watched word) keeps every word below `Hc` off the Keccak windows and
off `[ct, ct + 20)`; with `ct ≥ Hb` this keeps `PG` and the `aa` table, and the heap pointer returns to `Hc`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section cf
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat}

/-- `cca_wn` in whole-memory frame form. -/
theorem ccaF (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (hwK : ¬ KPW K Pd w) (hwO : ¬ MWin O 20 w) (M0 : Mem) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L M G => (CAL O L ∧ RG Lo Sc G) ∧ M = M0) (fun _ _ _ => False)
      (fun _ M' G' => RG Lo Sc G' ∧ ∀ x, x.toNat < Lo.toNat → ¬ KPW K Pd x → ¬ MWin O 20 x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_compute_contract_address) := by
  intro F s code dom aw sl H hH ⟨pre,hM⟩
  subst hM
  have win := fun (x : BitVec 64) (hx : x.toNat < Lo.toNat) (hk : ¬ KPW K Pd x) (ho : ¬ MWin O 20 x) =>
    cca_wn (w := x) (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
      (SKB := SKB) (Nj := Nj) hF hDF hcap Lo Sc K Pd O hK0 hPd0 hx (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))
      ho hLo8 F s code dom aw sl H hH pre
  obtain ⟨m,a,n,r,c,b⟩ := win w hw hwK hwO
  refine ⟨m,a,fun e => ⟨(n e).1,let ⟨_,_,h⟩ := (n e).2; h.elim⟩,fun v e => ?_,c,b⟩
  obtain ⟨H',hH',rg⟩ := r v e
  exact ⟨H',hH',rg,fun x hx hk ho => (win x hx hk ho).1⟩

#print axioms ccaF
end cf

section cp
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Hg Hb Nj : BitVec 64} {M0 : Mem}

theorem aqgd_call_cca_pg {LP : GA → Prop} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (K Pd NB : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hOut : Out w) (hP0Lo : P0.toNat ≤ Lo.toNat) (Taa Pa : BitVec 64) (hLoT : Lo.toNat ≤ Taa.toNat)
    (hLoHg : Lo.toNat ≤ Hg.toNat) (hPa : Pa.toNat ≤ Hg.toNat) (hgb : Hg.toNat ≤ Hb.toNat) (Ct : BitVec 64) (hCt : Hb.toNat ≤ Ct.toNat)
    (hCt8 : Ct.toNat % 8 = 0) (hCtE : Ct.toNat + 24 ≤ 33806089496)
    (hct : ∀ L, LP L → L.lookup (ofString "ct") = some (.val (.word Ct))) (e1 e2 : ExpHOL 64) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M)
      (fun L M G => (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M) RR
      (.call (some (none,none)) (ofString "compute_contract_address") [e1,e2,.var .local (ofString "ct")]) := by
  have hwP := (hOutSafe w hOut).2
  have hwK : ¬ KPW K Pd w := by
    rintro (h | h)
    · exact (hOutSafe w hOut).1.2.1 h
    · exact (hOutSafe w hOut).1.2.2.1 h
  have kpwLo : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → ¬ KPW K Pd x := by
    intro x hx
    rintro (h | h)
    · exact (hWsP0 x hx).2.1 h
    · exact (hWsP0 x hx).2.2.1 h
  refine aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (((CAL Ct L ∧ RG (hpOf G0') Sc G) ∧ M = M0') ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) ∧
        G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ((RG (hpOf G0') Sc G' ∧ ∀ x, x.toNat < (hpOf G0').toNat → ¬ KPW K Pd x → ¬ MWin Ct 20 x → M' x = M0' x) ∧
        ScrIs Sc G') ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    _ _ _ _ _ originalRuntimeCode_computeContractAddress_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨⟨_,⟨Hc,hHc,leb⟩,_,_,_⟩,_⟩
    rw [hpOf_eq hHc]
    refine aqgd_of_arenaFact (Φ := Hc.toNat % 8 = 0) (fun _ _ g aw ⟨_,hg⟩ => by
      subst hg; exact (jws_heap_facts aw.1.1.1 hHc).2.2) ?_
    intro hal
    exact aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (RR := fun _ M' G' => RG Hc Sc G' ∧ ∀ x, x.toNat < Hc.toNat → ¬ KPW K Pd x → ¬ MWin Ct 20 x → M' x = M0' x)
      (keepsBo_of_installed originalRuntimeCode_computeContractAddress_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_computeContractAddress_lookup (by decide))
      (aqgd_conseq (ccaF (w := w) (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J)
        (C := C) (SKB := SKB) (Nj := Nj) hF hDF hcap Hc Sc K Pd Ct hK0 hPd0 hal (by omega) hwK
        (mwin_belowS hCt8 (by omega) (by omega)) M0') (fun _ _ _ h => h) (fun _ _ _ h => h)
        (fun _ _ _ h => ⟨h,h.1.2⟩)))
      (fun _ _ _ ⟨a,_⟩ => a) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs aw H hG ⟨⟨lp,⟨Hc,hHc,_⟩,_,hn,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,hct _ lp] at ev3; subst ev3
    obtain ⟨a,b,_,rfl,rfl,_⟩ := entry3_words originalRuntimeCode_computeContractAddress_lookup lookup
    have e := callee_eq originalRuntimeCode_computeContractAddress_lookup lookup
    refine ⟨⟨⟨⟨⟨⟨a,by rw [e]; simp (config := {decide := true})⟩,⟨b,by rw [e]; simp (config := {decide := true})⟩,
      by rw [e]; simp (config := {decide := true})⟩,⟨Hc,hHc,by rw [hpOf_eq hHc]⟩,aw.2⟩,rfl⟩,hn⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨lp,pg⟩,tv⟩ ⟨⟨⟨⟨⟨H',hH',le'⟩,_⟩,fr⟩,_⟩,hn'⟩
    obtain ⟨Hc,hHc,leb⟩ := pg.1
    rw [hpOf_eq hHc] at le' fr
    refine ⟨⟨lp,pg_glob (pg_kp safe hOutSafe hkoWs pg (fun x hx hk => fr x (by omega) hk
      (mwin_belowS hCt8 (by omega) (by omega)))) ⟨H',hH',by omega⟩ hn'⟩,tabV_frame tv (fun x lo hi => ?_)⟩
    have := tv
    obtain ⟨_,_,_,_,_,_,_,_,_,_,lay,_,_,_⟩ := tv
    exact fr x (by omega) (kpwLo x (by omega)) (mwin_belowS hCt8 (by omega) (by omega))

#print axioms aqgd_call_cca_pg
end cp
end InitECandidate.Runtime
