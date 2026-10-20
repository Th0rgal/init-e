import InitECandidate.Runtime.PtSegTxhGD
import InitECandidate.Runtime.PtKoWsLGD
import InitECandidate.Runtime.PtSegBaseGDL
/-!
`process_transaction` spine drops 53-68: the access-list/blob/setcode/flag/index stores into `te`, the read-only
`tx_is_blob` / `tx_is_setcode`, `txh = alloc(32)`, `keccak256(enc.0, enc.1, txh)` (whole-memory frame: only the Keccak
state/pad windows and `[txh, txh + 32)` change, globals kept), and the hash/intrinsic stores; all keep `SI`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString




section kf
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Bo U Sc : BitVec 64} {G0 : GA}


end kf

section kc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Nj : BitVec 64} {M0 : Mem}

/-- `keccak256(e1, e2, out)` with a fresh 32-byte output block `FB out Lo 32`, keeping `SI`. -/
theorem aqgd_call_keccak_siL {LP : GA → Prop} (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
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
    exact ⟨lp,si_kpL safe hOutSafe hkoWs si (fun x hx hk => fr x hk (mwin_lo hLo8 lo (by omega) hx))⟩

#print axioms aqgd_call_keccak_siL




/-- Spine drops 53-68 of the actual `process_transaction`. -/
theorem ptSegTxhL {QM : Mem → GA → Prop} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
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
  refine aqgd_seq (aqgd_call_keccak_siL K Pd NB hK0 hPd0 safe hOutSafe hkoWs hOut hLo8 hw _ _ _ (fun _ h => h.2)) ?_
  refine aqgd_seq (sX 176#64 (by decide) _) ?_
  refine aqgd_seq (sX 184#64 (by decide) _) ?_
  refine aqgd_seq (sX 192#64 (by decide) _) ?_
  refine aqgd_seq aqgd_skip ?_
  exact aqgd_conseq hcont (fun _ _ _ h => ⟨h.1.1,h.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSegTxhL
end kc
end InitECandidate.Runtime
