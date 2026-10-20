import InitECandidate.Runtime.PtSegFinGD
import InitECandidate.Runtime.PtKoWsLGD
import InitECandidate.Runtime.PtGaPGGDL
import InitECandidate.Runtime.PtCcaPGGDL
/-!
`process_transaction` spine drops 90-97 (final phase): `empty = alloc(8)`, the creation branch (`get_account` at the
raised arena bound, `ct = alloc(24)`, `compute_contract_address`, six word stores into `m`) or the call branch (six
word stores into `m`), `st m + 136`, `htab_set(aa, lds (m + 32), 1)`, and the two table-pointer stores, ending in
`PXR` with `index` and `sender` at the `process_message_call` site.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString





section fin
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Nj Ts Bs : BitVec 64} {M0 : Mem}

/-- Spine drops 90-97 of the actual `process_transaction`, ending at the `process_message_call` site. -/
theorem ptSegFinL {QM : Mem → GA → Prop} {H0 : BitVec 64} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62)
    (hcap : 33806089496 ≤ DF) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x) (hOut : Out w)
    (Ix S Lo Mm Taa Tak : BitVec 64) (hP0Lo : P0.toNat ≤ Lo.toNat) (h0 : H0.toNat ≤ Lo.toNat)
    (hcLo : ∀ i, (c i).toNat < Lo.toNat) (hLoM : Lo.toNat ≤ Mm.toNat) (hMT : Mm.toNat + 176 ≤ Taa.toNat)
    (hLoT : Lo.toNat ≤ Taa.toNat) {cont : ProgHOL 64}
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ((((LTe Ix S Lo L ∧ L.lookup (ofString "m") = some (.val (.word Mm))) ∧
        L.lookup (ofString "aa") = some (.val (.word Taa))) ∧ L.lookup (ofString "ak") = some (.val (.word Tak))) ∧
        SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBu Taa Tak M G) (fun _ M G => QM M G) RR
      (.decCall (ofString "empty") .one (ofString "alloc") [(.const 8)]
        (.seq (.ite (.cmp .equal (.load .one (.op .add [(.var .local (ofString "tx")),(.const 152)])) (.const 0)) (.decCall (ofString "sa") .one (ofString "get_account") [(.var .local (ofString "sender"))] (.decCall (ofString "ct") .one (ofString "alloc") [(.const 24)] (.seq (.call (some (none,none)) (ofString "compute_contract_address") [(.var .local (ofString "sender")),(.op .sub [(.load .one (.op .add [(.var .local (ofString "sa")),(.const 0)])),(.const 1)]),(.var .local (ofString "ct"))]) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 32)]) (.var .local (ofString "ct"))) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 88)]) (.var .local (ofString "empty"))) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 96)]) (.const 0)) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 112)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 192)]))) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 120)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 200)]))) (.store (.op .add [(.var .local (ofString "m")),(.const 104)]) (.const 0)))))))))) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 32)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 152)]))) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 88)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 192)]))) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 96)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 200)]))) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 112)]) (.var .local (ofString "empty"))) (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 120)]) (.const 0)) (.store (.op .add [(.var .local (ofString "m")),(.const 104)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 152)])))))))))
        (.seq .skip
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 136)]) (.const 1))
        (.seq (.call (some (none,none)) (ofString "htab_set") [(.var .local (ofString "aa")),(.load .one (.op .add [(.var .local (ofString "m")),(.const 32)])),(.const 1)])
        (.seq .skip
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 152)]) (.var .local (ofString "aa")))
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 160)]) (.var .local (ofString "ak")))
        cont)))))))) := by
  have hwP := (hOutSafe w hOut).2
  have hw : w.toNat < Lo.toNat := by omega
  have hOutLo : ∀ x, Out x → x.toNat < Lo.toNat := fun x ho => by have := (hOutSafe x ho).2; omega
  let L0 := fun L : GA => ((LTe Ix S Lo L ∧ L.lookup (ofString "m") = some (.val (.word Mm))) ∧
    L.lookup (ofString "aa") = some (.val (.word Taa))) ∧ L.lookup (ofString "ak") = some (.val (.word Tak))
  have conv : ∀ L M G, (L0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBu Taa Tak M G →
      ∃ Hg Pa : BitVec 64, ((L0 L ∧ PG n c T Out ko D B Excl Lo Hg Hg Nj M0 M G) ∧
      TabV Taa Taa Pa M) ∧ (Pa.toNat ≤ Hg.toNat ∧ Lo.toNat ≤ Hg.toNat ∧ Taa.toNat + 72 ≤ Pa.toNat) := by
    intro L M G ⟨⟨l0,si⟩,⟨Pa,H,tv,hH,le1,_⟩⟩
    obtain ⟨H',hH',le'⟩ := si.1
    have e := heapIs_unique hH' hH
    subst e
    have hdrP : Taa.toNat + 72 ≤ Pa.toNat := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,lay,_,_,_⟩ := tv; exact lay.hdrP
    exact ⟨H',Pa,⟨⟨l0,pg_of_si hAB si hH⟩,tv⟩,le1,le',hdrP⟩
  refine aqgd_conseq (P := fun L M G => ∃ Hg Pa : BitVec 64, ((L0 L ∧ PG n c T Out ko D B Excl Lo Hg Hg Nj M0 M G) ∧
      TabV Taa Taa Pa M) ∧ (Pa.toNat ≤ Hg.toNat ∧ Lo.toNat ≤ Hg.toNat ∧ Taa.toNat + 72 ≤ Pa.toNat)) ?_ conv
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_exE (fun Hg => aqgd_exE (fun Pa => aqgd_pureE (fun ⟨hPa,hLoHg,hTP⟩ => ?_)))
  have hTg : Taa.toNat ≤ Hg.toNat := by omega
  -- word stores into m
  have stm : ∀ (LP : GA → Prop), (∀ L, LP L → L.lookup (ofString "m") = some (.val (.word Mm))) →
      ∀ (Hb : BitVec 64) (k : BitVec 64), k.toNat < 176 → ∀ (v : ExpHOL 64),
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals → EV s v = some x →
        ∃ y : BitVec 64, x = .val (.word y)) →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M)
        (fun L M G => (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M) RR
        (.store (.op .add [.var .local (ofString "m"),.const k]) v) :=
    fun LP hm Hb k hk v hv => aqgd_stw_pg Taa Pa hw hcLo hOutLo hTg _ v (fun s h => by
      have e : (Mm + k).toNat = Mm.toNat + k.toNat := by simp [BitVec.toNat_add]; omega
      exact ⟨Mm + k,ev_addc s _ Mm k (hm _ h),by omega,by omega⟩) hv
  have stm0 : ∀ (LP : GA → Prop), (∀ L, LP L → L.lookup (ofString "m") = some (.val (.word Mm))) →
      ∀ (Hb : BitVec 64) (k : BitVec 64), k.toNat < 176 → ∀ (v : ExpHOL 64),
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals → EV s v = some x →
        ∃ y : BitVec 64, x = .val (.word y)) →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G)
        (fun L M G => LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) RR
        (.store (.op .add [.var .local (ofString "m"),.const k]) v) :=
    fun LP hm Hb k hk v hv => aqgd_stw_pg0 hw hcLo hOutLo _ v (fun s h => by
      have e : (Mm + k).toNat = Mm.toNat + k.toNat := by simp [BitVec.toNat_add]; omega
      exact ⟨Mm + k,ev_addc s _ Mm k (hm _ h),by omega,by omega⟩) hv
  have ldw : ∀ (LP : GA → Prop) (e : ExpHOL 64) {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals →
      EV s (.load .one e) = some x → ∃ y : BitVec 64, x = .val (.word y) :=
    fun _ e _ s x _ ev => ev_load_one_word s _ x ev
  have cw : ∀ (LP : GA → Prop) (k : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals →
      EV s (.const k) = some x → ∃ y : BitVec 64, x = .val (.word y) :=
    fun _ k _ s x _ ev => ⟨k,by simp [EV,evalHOLExact] at ev; exact ev.symm⟩
  have vw : ∀ (LP : GA → Prop) (nm : MlS) (X : BitVec 64), (∀ L, LP L → L.lookup nm = some (.val (.word X))) →
      ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals →
      EV s (.var .local nm) = some x → ∃ y : BitVec 64, x = .val (.word y) :=
    fun _ nm X hX _ s x h ev => ⟨X,by simp [EV,evalHOLExact,hX _ h] at ev; exact ev.symm⟩
  -- empty = alloc(8)
  refine aqgd_decCall_allocC_pg (LP := L0) (LP' := L0) _ 8#64 Taa Pa
    (fun L v h => ⟨⟨⟨lte_upd h.1.1.1 _ v (by decide) (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact h.1.1.2⟩,by rw [lookup_update_ne' _ _ (by decide)]; exact h.1.2⟩,
      by rw [lookup_update_ne' _ _ (by decide)]; exact h.2⟩) (fun E _ _ _ => ?_) (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_conseq (P := fun L M G => (LF Ix S Lo Mm Taa Tak L ∧ PG n c T Out ko D B Excl Lo Hg Hg Nj M0 M G) ∧
    TabV Taa Taa Pa M) ?_ (fun _ _ _ ⟨⟨⟨l0,he⟩,pg⟩,tv⟩ => ⟨⟨⟨l0,E,he⟩,pg⟩,tv⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  let Qi := fun L M G => ∃ Hb : BitVec 64, ((LF Ix S Lo Mm Taa Tak L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧
    TabV Taa Taa Pa M) ∧ Hg.toNat ≤ Hb.toNat
  have hmF : ∀ L, LF Ix S Lo Mm Taa Tak L → L.lookup (ofString "m") = some (.val (.word Mm)) :=
    fun L h => h.1.1.1.2
  refine aqgd_seq (Q := Qi) (aqgd_iteT _ ?_ ?_) ?_
  · -- creation branch
    refine aqgd_decCall_getAccount_pgL (LP := LF Ix S Lo Mm Taa Tak) (LP' := LF Ix S Lo Mm Taa Tak) (Q := Qi)
      _ (ofString "sender") Taa Pa hAB hAo hBo hTs hBs hcA hcB hOut hwP hP0Lo hLoT hLoHg hPa (le_refl _) K Pd NB
      hK0 hPd0 hNB0 safe hOutSafe hkoWs hWsP0 (fun L h => ⟨S,h.1.1.1.1.1 (ofString "sender",S) (by simp)⟩)
      (fun L y h => lf_upd h _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun Hb' leb => ?_)
      (fun _ _ _ _ _ _ _ ⟨Hb,⟨⟨lf,pg⟩,tv⟩,le⟩ => ⟨Hb,⟨⟨lf_res lf _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),pg⟩,tv⟩,le⟩)
    refine aqgd_decCall_allocC_pg (LP := LF Ix S Lo Mm Taa Tak) (LP' := LF Ix S Lo Mm Taa Tak) (Q := Qi) _ 24#64 Taa Pa
      (fun L v h => lf_upd h _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun Ct hCt hCtE hCt8 => ?_)
      (fun _ _ _ _ _ _ _ ⟨Hb,⟨⟨lf,pg⟩,tv⟩,le⟩ => ⟨Hb,⟨⟨lf_res lf _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),pg⟩,tv⟩,le⟩)
    let LC := fun L : GA => LF Ix S Lo Mm Taa Tak L ∧ L.lookup (ofString "ct") = some (.val (.word Ct))
    have hmC : ∀ L, LC L → L.lookup (ofString "m") = some (.val (.word Mm)) := fun L h => hmF L h.1
    refine aqgd_seq (aqgd_call_cca_pgL (LP := LC) hF hDF hcap K Pd NB hK0 hPd0 safe hOutSafe hkoWs hWsP0 hOut hP0Lo
      Taa Pa hLoT hLoHg hPa (by omega) Ct hCt hCt8 (by have : (24#64).toNat = 24 := rfl; omega) (fun L h => h.2) _ _) ?_
    refine aqgd_seq (stm LC hmC Hb' 32#64 (by decide) _ (vw LC _ Ct (fun L h => h.2))) ?_
    refine aqgd_seq (stm LC hmC Hb' 88#64 (by decide) _ ?_) ?_
    · intro F s x h ev
      obtain ⟨E',he⟩ := h.1.2
      exact ⟨E',by simp [EV,evalHOLExact,he] at ev; exact ev.symm⟩
    refine aqgd_seq (stm LC hmC Hb' 96#64 (by decide) _ (cw LC 0#64)) ?_
    refine aqgd_seq (stm LC hmC Hb' 112#64 (by decide) _ (ldw LC _)) ?_
    refine aqgd_seq (stm LC hmC Hb' 120#64 (by decide) _ (ldw LC _)) ?_
    exact aqgd_conseq (stm LC hmC Hb' 104#64 (by decide) _ (cw LC 0#64)) (fun _ _ _ h => h)
      (fun _ _ _ ⟨⟨lc,pg⟩,tv⟩ => ⟨Hb',⟨⟨lc.1,pg⟩,tv⟩,leb⟩) (fun _ _ _ h => h)
  · -- call branch
    let LFp := LF Ix S Lo Mm Taa Tak
    refine aqgd_seq (stm LFp hmF Hg 32#64 (by decide) _ (ldw LFp _)) ?_
    refine aqgd_seq (stm LFp hmF Hg 88#64 (by decide) _ (ldw LFp _)) ?_
    refine aqgd_seq (stm LFp hmF Hg 96#64 (by decide) _ (ldw LFp _)) ?_
    refine aqgd_seq (stm LFp hmF Hg 112#64 (by decide) _ ?_) ?_
    · intro F s x h ev
      obtain ⟨E',he⟩ := h.2
      exact ⟨E',by simp [EV,evalHOLExact,he] at ev; exact ev.symm⟩
    refine aqgd_seq (stm LFp hmF Hg 120#64 (by decide) _ (cw LFp 0#64)) ?_
    exact aqgd_conseq (stm LFp hmF Hg 104#64 (by decide) _ (ldw LFp _)) (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨Hg,h,le_refl _⟩) (fun _ _ _ h => h)
  refine aqgd_exE (fun Hb => ?_)
  refine aqgd_conseq (P := fun L M G => ((LF Ix S Lo Mm Taa Tak L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧
    TabV Taa Taa Pa M) ∧ Hg.toNat ≤ Hb.toNat) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_pureE (fun hgb => ?_)
  let LFp := LF Ix S Lo Mm Taa Tak
  refine aqgd_seq aqgd_skip ?_
  refine aqgd_seq (stm LFp hmF Hb 136#64 (by decide) _ (cw LFp 1#64)) ?_
  refine aqgd_seq (aqgd_call_htabSet_pg (LP := LFp) _ _ _ Taa Pa hLoT hPa hgb hw hcLo hOutLo
    (fun L h => h.1.1.2)) ?_
  refine aqgd_seq aqgd_skip ?_
  refine aqgd_seq (stm0 LFp hmF Hb 152#64 (by decide) _ (vw LFp _ Taa (fun L h => h.1.1.2))) ?_
  refine aqgd_seq (stm0 LFp hmF Hb 160#64 (by decide) _ (vw LFp _ Tak (fun L h => h.1.2))) ?_
  refine aqgd_conseq hcont (fun L M G ⟨lf,pg⟩ => ⟨⟨lf.1.1.1.1.1 (ofString "index",Ix) (by simp),S,
    lf.1.1.1.1.1 (ofString "sender",S) (by simp)⟩,pxr_of_pg (by omega) pg⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSegFinL
end fin
end InitECandidate.Runtime
