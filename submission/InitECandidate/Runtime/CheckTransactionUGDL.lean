import InitECandidate.Runtime.CheckTransactionUGD
import InitECandidate.Runtime.PtKoWsLGD
/-!
`check_transaction` over the arena that also pins the `u256_ws` workspace pointer: `checkTransaction_frameCUL` gives
`FrameCU` for the actual `check_transaction` from the `FrameCU` of `calculate_blob_gas_price` (proved in
`BlobPriceFrameGD`). Callee specs over the plain arena lift through the whole-program `u256_ws` keep decision.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section lift
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB U : BitVec 64}



end lift

section cxu
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB H0 Nj Ts Bs U : BitVec 64} {M0 : Mem} {Q : Mem → GA → Prop}


/-- The actual `get_account(x)` declared call keeping `CX`. -/
theorem aqgd_decCall_getAccountXUL (name : MlS) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hOut : Out w) (hwP : w.toNat < P0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
    (hcont : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR cont) :
    AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR
      (.decCall name .one (ofString "get_account") arguments cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ (H1 : BitVec 64) (l : Fin n → TLay), HeapIs G0' H1 ∧
        RegPure n c T Out H1 l ∧ RegMem n c T l M0' ∧ TCont D B M0' (T ko) (l ko) ∧
        (∀ x, (l ko).arr x → x.toNat < H1.toNat) ∧
        (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
          ((Reg n c T Out H' M' ∧ H1.toNat ≤ H'.toNat) ∧
            ∀ x, GaKeep SP0 P0 FM K Pd NB Out (T ko) (l ko) x → M' x = M0' x)))
    (Pc := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (Qc := fun _ M G => Q M G)
    _ _ _ _ _ _ _ originalRuntimeCode_account_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hcont
    (fun _ _ _ _ _ _ _ h => h)
  · intro L0 M0' G0' ⟨H1,hH,h01,⟨l,pure,mem,tc,ab⟩,hn,_⟩
    refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H1.toNat) (fun L M g aw ⟨_,_,hg⟩ => jws_heap_lo aw.1 (hg ▸ hH)) ?_
    intro p1
    refine aqgd_conseq (aqgd_jwsu (aqgd_jws (aqgd_of_aqg (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_account_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (accountRegT_aqmh n c T kA kB ko hAB hAo hBo Ts Bs hTs hBs hcA hcB Out hOut H1 p1 K Pd NB hK0 hPd0 hNB0
        safe (hOutSafe w hOut).1 hwP l pure M0' mem ab))))
      (keepsSkBuf_of_installed originalRuntimeCode_account_lookup (by decide)))
      (keepsWs_of_installed originalRuntimeCode_account_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨hn,H1,hH,⟨ha,rfl,l,reg_of pure mem,pure.2.1,pure.2.2⟩,rfl⟩
    · intro v M' G' ⟨post,_⟩
      exact ⟨H1,l,hH,pure,mem,tc,ab,post⟩
  · intro F s values callee rs _ H _ _ _ _ lookup
    exact ⟨callee_one originalRuntimeCode_account_lookup lookup,rfl,rfl⟩
  · intro L M G v M' G' ⟨H1,hH,hle,_,_,fr⟩ ⟨H1',l,hH',pure,mem,tc,ab,hn',H',hH2,⟨reg,hle'⟩,frG⟩ _
    have e := heapIs_unique hH hH'
    subst e
    have keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        M' x = M x := fun x hx => frG x (Or.inl ⟨hx,hkoWs (l ko) _ (pure.1 ko).1 x hx⟩)
    exact ⟨H',hH2,le_trans hle hle',regT_of_reg l pure tc ab reg hle' keepT,hn',
      fun x ho hxe => (frG x (Or.inr ⟨ho,hOutSafe x ho⟩)).trans (fr x ho hxe)⟩

/-- The actual `get_code(code_hash, addr)` declared call keeping `CX` (key-buffer writes inside `Excl`). -/
theorem aqgd_decCall_getCodeXUL (name : MlS) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (ne : k40 ≠ ko) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hc40 : c k40 = Ts + 40#64) (hwP : w.toNat < P0.toNat) (hOut : Out w)
    (hwS : ¬ SkWin SKB w) (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSE : ∀ x, SkWin SKB x → Excl x)
    (hcont : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR cont) :
    AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR
      (.decCall name (.comb [.one,.one]) (ofString "get_code") arguments cont) := by
  refine aqgd_decCallSpec (Vn' := fun x => x ≠ ofString "w" ∧ x ≠ ofString "c")
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      ((∃ Ch : BitVec 64, L.lookup (ofString "code_hash") = some (.val (.word Ch))) ∧
        (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A)))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1 : BitVec 64, HeapIs G0' H1 ∧ GCPost n c T Out ko D B SKB H1 Nj M0' M' G')
    (Pc := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (Qc := fun _ M G => Q M G)
    _ _ _ _ _ _ _ originalRuntimeCode_getCode_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hcont
    (fun _ _ _ _ _ _ _ h => h)
  · intro L0 M0' G0' ⟨H1,hH,h01,reg,hn,_⟩
    refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H1.toNat) (fun L M g aw ⟨_,_,hg⟩ => jws_heap_lo aw.1 (hg ▸ hH)) ?_
    intro p1
    refine aqgd_conseq (aqgd_jwsu (getCodeT_aqgd (T := T) (H0 := H1) (M0 := M0') (Nj := Nj) ne hTs hc40 p1 hwP hOut hwS
      hSO) (keepsWs_of_installed originalRuntimeCode_getCode_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨ha,reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro F s values callee rs _ H _ _ _ _ lookup
    obtain ⟨Ch,A,h1,h2⟩ := callee_two originalRuntimeCode_getCode_lookup (by decide) lookup
    exact ⟨⟨⟨Ch,h1⟩,⟨A,h2⟩⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨H1,hH,hle,_,_,fr⟩ ⟨H1',hH',H',hH2,hle',reg',hn',fr'⟩ _
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨H',hH2,le_trans hle hle',reg',hn',fun x ho hx => (fr' x ho (fun k => hx (hSE x k))).trans (fr x ho hx)⟩

#print axioms aqgd_decCall_getAccountXUL
#print axioms aqgd_decCall_getCodeXUL
end cxu

section cku
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Ts Bs H0 Nj U : BitVec 64} {M0 : Mem}
  (fcBgp : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price))
  (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
  (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
  (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
  (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hOut : Out w) (hwP : w.toNat < P0.toNat) (K Pd NB : BitVec 64)
  (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
  (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
  (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
  (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
  (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
  (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
  (ne40 : k40 ≠ ko) (hc40 : c k40 = Ts + 40#64) (hwS : ¬ SkWin SKB w)
  (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSE : ∀ x, SkWin SKB x → Excl x)
include fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 28. -/
theorem lku28L : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK28 := by
  unfold ckK28
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256AddCarry_lookup (memoryFrame_of_good originalRuntimeCode_u256AddCarry_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_add_carry) (by body_check Guest.guestFn_u256_add_carry) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_decCall_getCodeXUL _ _ ne40 hTs hc40 hwP hOut hwS hSO hSE ?_
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_memeq_lookup (memoryFrame_of_good originalRuntimeCode_memeq_lookup (by decide) (by decide)) (by body_check Guest.guestFn_memeq) (by body_check Guest.guestFn_memeq) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_isValidDelegation_lookup (memoryFrame_of_good originalRuntimeCode_isValidDelegation_lookup (by decide) (by decide)) (by body_check Guest.guestFn_is_valid_delegation) (by body_check Guest.guestFn_is_valid_delegation) ?_
      refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
      · exact aqgd_raise _ _
      · exact aqgd_skip
    · exact aqgd_skip
  exact aqgd_return _ (fun _ _ _ _ _ h _ _ => h)

/-- Frame of `check_transaction` from spine position 20. -/
theorem lku20L : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK20 := by
  unfold ckK20
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
      · exact aqgd_raise _ _
      · exact aqgd_skip
    · exact aqgd_skip
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256FitsWord_lookup (memoryFrame_of_good originalRuntimeCode_u256FitsWord_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_fits_word) (by body_check Guest.guestFn_u256_fits_word) ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  exact lku28L fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 19. -/
theorem lku19L : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK19 := by
  unfold ckK19
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · refine aqgd_dec_x _ _ _ ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_dec_x _ _ _ ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_while_x _ ?_
        refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
        · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
          · exact aqgd_raise _ _
          · exact aqgd_skip
        exact aqgd_assign_x _ _
      refine aqgd_decCall_fcXU _ _ _ _ _ _ _ originalRuntimeCode_blobGasPrice_lookup (by simp) fcBgp ?_
      refine aqgd_dec_x _ _ _ ?_
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide)) (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_assign_x _ _
        · exact aqgd_skip
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256AddCarry_lookup (memoryFrame_of_good originalRuntimeCode_u256AddCarry_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_add_carry) (by body_check Guest.guestFn_u256_add_carry) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_assign_x _ _
        · exact aqgd_skip
      exact aqgd_assign_x _ _
    · exact aqgd_skip
  exact lku20L fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 16. -/
theorem lku16L : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK16 := by
  unfold ckK16
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide)) (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  exact lku19L fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 15. -/
theorem lku15L : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK15 := by
  unfold ckK15
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · refine aqgd_dec_x _ _ _ ?_
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · exact aqgd_assign_x _ _
      exact aqgd_assign_x _ _
    · refine aqgd_dec_x _ _ _ ?_
      refine aqgd_dec_x _ _ _ ?_
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Sub_lookup (memoryFrame_of_good originalRuntimeCode_u256Sub_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_sub) (by body_check Guest.guestFn_u256_sub) ?_
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_dec_x _ _ _ ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_assign_x _ _
        · exact aqgd_skip
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · exact aqgd_callAssign_x _ _ _ _ _ _ originalRuntimeCode_u256Add_lookup (memoryFrame_of_good originalRuntimeCode_u256Add_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_add) (by body_check Guest.guestFn_u256_add)
      exact aqgd_assign_x _ _
  exact lku16L fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 10. -/
theorem lku10L : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK10 := by
  unfold ckK10
  refine aqgd_decCall_getAccountXUL _ _ hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  exact lku15L fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 0. -/
theorem lku0L : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK0 := by
  unfold ckK0
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_min_lookup (memoryFrame_of_good originalRuntimeCode_min_lookup (by decide) (by decide)) (by body_check Guest.guestFn_min) (by body_check Guest.guestFn_min) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_totalBlobGas_lookup (memoryFrame_of_good originalRuntimeCode_totalBlobGas_lookup (by decide) (by decide)) (by body_check Guest.guestFn_calculate_total_blob_gas) (by body_check Guest.guestFn_calculate_total_blob_gas) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  exact lku10L fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

end cku

section finu
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Ts Bs U : BitVec 64}

/-- Frame contract of the actual `check_transaction(tx, sender)`: from the content-carrying registry at any entry
heap, every return keeps the registry at the exit heap, the journal counter, and every outside word outside `Excl`
(the key buffer `SkWin SKB` lies in `Excl`). Real specs: `get_account`, `get_code`, and the read-only callees `min`,
`calculate_total_blob_gas`, `u256_lt`, `u256_sub`, `u256_add`, `u256_add_carry`, `fee_mul`, `u256_fits_word`,
`memeq`, `is_valid_delegation` (whole-program memory/globals decisions). Remaining temporary premise: the
`calculate_blob_gas_price` frame contract `fcBgp`. -/
theorem checkTransaction_frameCUL
    (fcBgp : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price))
    (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hOut : Out w) (hwP : w.toNat < P0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
    (ne40 : k40 ≠ ko) (hc40 : c k40 = Ts + 40#64) (hwS : ¬ SkWin SKB w)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSE : ∀ x, SkWin SKB x → Excl x) :
    FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_check_transaction) := by
  intro H0 Nj M0
  rw [checkTransaction_body_eq]
  exact aqgd_noFall (aqgd_conseq (lku0L (H0 := H0) (Nj := Nj) (M0 := M0) fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP
      K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE)
    (fun _ M G ⟨reg,hM,hH,hn⟩ => ⟨H0,hH,le_refl _,reg,hn,fun x _ _ => by rw [hM]⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h))

#print axioms checkTransaction_frameCUL
end finu
end InitECandidate.Runtime
