import InitECandidate.Runtime.PtSegKeysGD
import InitECandidate.Runtime.OriginalTxIsBlobCode
/-!
`process_transaction` spine drops 53-68: the access-list/blob/setcode/flag/index stores into `te`, the read-only
`tx_is_blob` / `tx_is_setcode`, `txh = alloc(32)`, `keccak256(enc.0, enc.1, txh)` (whole-memory frame: only the Keccak
state/pad windows and `[txh, txh + 32)` change, globals kept), and the hash/intrinsic stores; all keep `SI`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A call of a three-word-parameter function proceeds only with three words. -/
theorem entry3_words {f p q r : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,.one),(q,.one),(r,.one)],bd,rs0)) {v1 v2 v3 : ValueHOL 64}
    {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (h : lookupCodeHOLFinite originalRuntimeCode.lookup f [v1,v2,v3] = some (body,callee,rs)) :
    ∃ a b c : BitVec 64, v1 = .val (.word a) ∧ v2 = .val (.word b) ∧ v3 = .val (.word c) := by
  have hs := lookupCode_shapes inst h
  simp only [List.zip_cons_cons,List.zip_nil_right,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at hs
  obtain ⟨h1,h2,h3⟩ := hs
  obtain ⟨a,rfl⟩ := word_of_shape_one ((shapeEqHOL_eq_true _ _).mp h1).symm
  obtain ⟨b,rfl⟩ := word_of_shape_one ((shapeEqHOL_eq_true _ _).mp h2).symm
  obtain ⟨c,rfl⟩ := word_of_shape_one ((shapeEqHOL_eq_true _ _).mp h3).symm
  exact ⟨a,b,c,rfl,rfl,rfl⟩

#print axioms entry3_words

theorem jwsbus_keccak {SP0 P0 FM J C SKB Bo U Sc K Pd : BitVec 64} {G0 g : GA}
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (h : JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc g) :
    g.lookup (ofString "keccak_st") = some (.val (.word K)) ∧ g.lookup (ofString "keccak_pad") = some (.val (.word Pd)) :=
  ⟨(h.1.1.1.1.1.2.2.2 _ (by decide)).1.trans hK0,(h.1.1.1.1.1.2.2.2 _ (by decide)).1.trans hPd0⟩

section kf
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Bo U Sc : BitVec 64} {G0 : GA}

/-- The actual `keccak256(p, n, out)` (whole-memory frame form): globals kept, and every word outside the Keccak
state/pad windows and `[out, out + 32)` unchanged. -/
theorem keccakF (K Pd O Pp N : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hwK : ¬ KPW K Pd w) (hwO : ¬ MWin O 32 w)
    (M0 : Mem) (Gk : GA) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => KL0 Pp N O L ∧ M = M0 ∧ G = Gk) (fun _ _ _ => True)
      (fun _ M' G' => G' = Gk ∧ ∀ x, ¬ KPW K Pd x → ¬ MWin O 32 x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_keccak256) := by
  intro F s code dom aw sl H hH ⟨kl,hM,hG⟩
  subst hM
  unfold GIs at hH; subst hH hG
  have hA : ∀ g, JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc g → g.lookup (ofString "keccak_st") = some (.val (.word K)) ∧
      g.lookup (ofString "keccak_pad") = some (.val (.word Pd)) := fun g h => jwsbus_keccak hK0 hPd0 h
  have win := fun (x : BitVec 64) (hx : ¬ KPW K Pd x) (hxO : ¬ MWin O 32 x) =>
    keccak_wn (w := x) (D := D) (B := B) K Pd hA Pp N O (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h)) hxO
      F s code dom aw sl _ rfl kl
  have glob := evaluate_keepsGA goodGA goodGA_bodies _ (keepsGA_of_installed originalRuntimeCode_keccak_lookup
    (by decide)) s code
  obtain ⟨m,a,n,r,c,b⟩ := win w hwK hwO
  refine ⟨m,a,fun e => ⟨(n e).1,_,rfl,trivial⟩,fun v e => ⟨_,rfl,glob,fun x hx hxO => (win x hx hxO).1⟩,c,b⟩

#print axioms keccakF
end kf

section kc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Nj : BitVec 64} {M0 : Mem}

/-- `keccak256(e1, e2, out)` with a fresh 32-byte output block `FB out Lo 32`, keeping `SI`. -/
theorem aqgd_call_keccak_si {LP : GA → Prop} (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hOut : Out w) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (e1 e2 : ExpHOL 64) (out : MlS)
    (hfb : ∀ L, LP L → FB out Lo 32 L) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
      (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) RR
      (.call (some (none,none)) (ofString "keccak256") [e1,e2,.var .local out]) := by
  have hwK : ¬ KPW K Pd w := by
    rintro (h | h)
    · exact (hOutSafe w hOut).1.2.1 h
    · exact (hOutSafe w hOut).1.2.2.1 h
  refine aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ Pp N : BitVec 64, KL0 Pp N (wordOf L0 out) L) ∧ M = M0' ∧ G = G0')
    (RRe := fun (L0 : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G' = G0' ∧ ∀ x, ¬ KPW K Pd x → ¬ MWin (wordOf L0 out) 32 x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_keccak_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨lp,_⟩
    obtain ⟨O,hO,lo,hi⟩ := hfb L0 lp
    rw [wordOf_eq hO]
    refine aqgd_conseq (P := fun L M G => ∃ Pp N : BitVec 64, KL0 Pp N O L ∧ M = M0' ∧ G = G0') ?_
      (fun _ _ _ ⟨⟨Pp,N,kl⟩,hm⟩ => ⟨Pp,N,kl,hm⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    exact aqgd_exE (fun Pp => aqgd_exE (fun N => keccakF K Pd O Pp N hK0 hPd0 hwK
      (mwin_lo hLo8 lo (by omega) hw) M0' G0'))
  · intro F s values callee rs _ H hG ⟨lp,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨O,hO,_,_⟩ := hfb _ lp
    obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,hO] at ev3; subst ev3
    obtain ⟨a,b,_,rfl,rfl,_⟩ := entry3_words originalRuntimeCode_keccak_lookup lookup
    have e := callee_eq originalRuntimeCode_keccak_lookup lookup
    rw [wordOf_eq hO]
    exact ⟨⟨a,b,by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),
      by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,si⟩ ⟨hG,fr⟩
    subst hG
    obtain ⟨O,hO,lo,hi⟩ := hfb L lp
    rw [wordOf_eq hO] at fr
    exact ⟨lp,si_kp safe hOutSafe hkoWs si (fun x hx hk => fr x hk (mwin_lo hLo8 lo (by omega) hx))⟩

#print axioms aqgd_call_keccak_si

/-- `name = alloc(N)` for a constant size `N`, keeping `SI`: the new local is a block `[Hb, Hb + N)` at or above
`Lo`, 8-aligned, ending at most at `HEAP_END`. -/
theorem aqgd_decCall_allocC_si {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name : MlS) (Nn : BitVec 64)
    {cont : ProgHOL 64}
    (hup : ∀ L (Hb : BitVec 64), LP L → Lo.toNat ≤ Hb.toNat → Hb.toNat + Nn.toNat ≤ 33806089496 → Hb.toNat % 8 = 0 →
      LP' (L.update (name,.val (.word Hb))))
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP' L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) Q2 RR
      (.decCall name .one (ofString "alloc") [.const Nn] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ Hb : BitVec 64, HeapIs G0' Hb ∧ Hb.toNat % 8 = 0 ∧ Hb.toNat ≤ 33806089496 ∧
        (v = .val (.word Hb) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ Hb.toNat + Nn.toNat ≤ H'.toNat ∧
          H'.toNat ≤ 33806089496) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := fun L M G => LP' L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (Qc := Q)
    _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hcont hres
  · intro L0 M0' G0' ⟨_,⟨Hb,hH,_⟩,_,hn,_⟩
    refine aqgd_of_arenaFact (Φ := (P0.toNat ≤ Hb.toNat ∧ Hb.toNat ≤ 33806089496 ∧ Hb.toNat % 8 = 0) ∧ ScrIs Sc G0')
      (fun _ _ g aw ⟨_,_,hg⟩ => by subst hg; exact ⟨jws_heap_facts aw.1.1.1 hH,aw.2⟩) ?_
    intro ⟨⟨_,hcapH,hal⟩,hsc⟩
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
    · intro v M' G' ⟨hn',H',hH',eM,ev,_,_,c1,c2,_,_⟩
      exact ⟨Hb,hH,hal,hcapH,⟨ev,eM,H',hH',c1,c2⟩,hn'⟩
  · intro F s values callee rs _ H _ _ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,si⟩ ⟨Hb,hH,hal,hcap,⟨ev,eM,H',hH',le',hE⟩,hn'⟩ _
    subst ev eM
    obtain ⟨H1,hH1,le1⟩ := si.1
    have e := heapIs_unique hH1 hH
    subst e
    exact ⟨hup L H1 lp le1 (by omega) hal,si_glob si ⟨H',hH',by omega⟩ hn'⟩

#print axioms aqgd_decCall_allocC_si


/-- Spine drops 53-68 of the actual `process_transaction`. -/
theorem ptSegTxh {QM : Mem → GA → Prop} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hOut : Out w) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (Ix S : BitVec 64) {cont : ProgHOL 64}
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (fun _ M G => QM M G) RR
      (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 96)]) (.var .local (ofString "al_addrs")))
      (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 104)]) (.op .add [(.var .local (ofString "nal")),(.const 1)]))
      (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 112)]) (.var .local (ofString "al_keys")))
      (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 120)]) (.var .local (ofString "nkeys")))
      (.decCall (ofString "isb") .one (ofString "tx_is_blob") [(.var .local (ofString "tx"))]
      (.seq (.ite (.cmp .notEqual (.var .local (ofString "isb")) (.const 0)) (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 128)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 256)]))) (.store (.op .add [(.var .local (ofString "te")),(.const 136)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 264)])))) .skip)
      (.decCall (ofString "issc") .one (ofString "tx_is_setcode") [(.var .local (ofString "tx"))]
      (.seq (.ite (.cmp .notEqual (.var .local (ofString "issc")) (.const 0)) (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 144)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 272)]))) (.store (.op .add [(.var .local (ofString "te")),(.const 152)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 280)])))) .skip)
      (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 160)]) (.const 1))
      (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 168)]) (.var .local (ofString "index")))
      (.decCall (ofString "txh") .one (ofString "alloc") [(.const 32)]
      (.seq (.call (some (none,none)) (ofString "keccak256") [(.rfield 0 (.var .local (ofString "enc"))),(.rfield 1 (.var .local (ofString "enc"))),(.var .local (ofString "txh"))])
      (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 176)]) (.var .local (ofString "txh")))
      (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 184)]) (.rfield 0 (.var .local (ofString "intrinsic"))))
      (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 192)]) (.rfield 1 (.var .local (ofString "intrinsic"))))
      (.seq .skip cont)))))))))))))))) := by
  have hD : DF + 8 ≤ 2 ^ 64 := by omega
  have st := fun (LP : GA → Prop) (hte : ∀ L, LP L → FB (ofString "te") Lo 200 L) (k : BitVec 64)
      (hk : k.toNat < 200) (v : ExpHOL 64) =>
    aqgd_stFB_si (D := D) (B := B) (A := JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) (w := w) (Vn := fun _ => False)
      (RR := RR) (n := n) (c := c) (T := T) (Out := Out) (ko := ko) (Excl := Excl) (Nj := Nj) (M0 := M0)
      (LP := LP) hF hD hw (ofString "te") 200 k hk hte v
  have sT := st (LTe Ix S Lo) (fun _ h => h.2)
  refine aqgd_seq (sT 96#64 (by decide) _) ?_
  refine aqgd_seq (sT 104#64 (by decide) _) ?_
  refine aqgd_seq (sT 112#64 (by decide) _) ?_
  refine aqgd_seq (sT 120#64 (by decide) _) ?_
  refine aqgd_decCall_mf (I' := fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    _ _ _ _ _ _ _ originalRuntimeCode_txIsBlob_lookup (by simp)
    (memoryFrame_of_good originalRuntimeCode_txIsBlob_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_tx_is_blob) (by body_check Guest.guestFn_tx_is_blob)
    (fun L M G v pre => ⟨lte_upd pre.1 _ v (by decide) (by decide) (by decide),pre.2⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (sT 128#64 (by decide) _) (sT 136#64 (by decide) _)) aqgd_skip) ?_
  refine aqgd_decCall_mf (I' := fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    _ _ _ _ _ _ _ originalRuntimeCode_txIsSetcode_lookup (by simp)
    (memoryFrame_of_good originalRuntimeCode_txIsSetcode_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_tx_is_setcode) (by body_check Guest.guestFn_tx_is_setcode)
    (fun L M G v pre => ⟨lte_upd pre.1 _ v (by decide) (by decide) (by decide),pre.2⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (sT 144#64 (by decide) _) (sT 152#64 (by decide) _)) aqgd_skip) ?_
  refine aqgd_seq (sT 160#64 (by decide) _) ?_
  refine aqgd_seq (sT 168#64 (by decide) _) ?_
  refine aqgd_decCall_allocC_si (LP' := fun L => LTe Ix S Lo L ∧ FB (ofString "txh") Lo 32 L) _ 32#64
    (fun L Hb lp le hi _ => ⟨lte_upd lp _ _ (by decide) (by decide) (by decide),fb_new L _ le hi⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  have sX := st (fun L => LTe Ix S Lo L ∧ FB (ofString "txh") Lo 32 L) (fun _ h => h.1.2)
  refine aqgd_seq (aqgd_call_keccak_si K Pd NB hK0 hPd0 safe hOutSafe hkoWs hOut hLo8 hw _ _ _ (fun _ h => h.2)) ?_
  refine aqgd_seq (sX 176#64 (by decide) _) ?_
  refine aqgd_seq (sX 184#64 (by decide) _) ?_
  refine aqgd_seq (sX 192#64 (by decide) _) ?_
  refine aqgd_seq aqgd_skip ?_
  exact aqgd_conseq hcont (fun _ _ _ h => ⟨h.1.1,h.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSegTxh
end kc
end InitECandidate.Runtime
