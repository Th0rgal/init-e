import InitECandidate.Runtime.AccountWritersGD
import InitECandidate.Runtime.OriginalPtSufCode
/-!
The actual `clear_account_preserving_balance(addr)` over the content-carrying registry `RegT`: `destroy_storage(addr)`
(`DSPost`), then `get_account`, a fresh copy, the stores `a + 0 = 0` and `a + 48 = empty_code_hash` into the copy, and
the original `modify_state_commit` (`DAPost`). The tail is the `increment_nonce` proof with the two stores.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The tail of `clear_account_preserving_balance` after `destroy_storage(addr)`. -/
def clearTail : ProgHOL 64 :=
  .decCall (ofString "a") .one (ofString "get_account") [(.var .local (ofString "addr"))]
    (.seq (.call (some ((some (.local,ofString "a")),none)) (ofString "acct_copy") [(.var .local (ofString "a"))])
    (.seq (.store (.op .add [(.var .local (ofString "a")),(.const 0)]) (.const 0))
    (.seq (.store (.op .add [(.var .local (ofString "a")),(.const 48)]) (.var .global (ofString "empty_code_hash")))
    (.seq (.call (some (none,none)) (ofString "modify_state_commit") [(.var .local (ofString "addr")),(.var .local (ofString "a"))])
      (.return (.const 0))))))

theorem source_clearAcctPB_body : sourceFunctionBody Guest.guestFn_clear_account_preserving_balance =
    .seq (.call (some (none,none)) (ofString "destroy_storage") [(.var .local (ofString "addr"))]) clearTail := by
  unfold sourceFunctionBody clearTail
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem clr_heap_le {SP0 P0 FM J C SKB H : BitVec 64} {G0 g : GA} (h : JWS SP0 P0 FM G0 J C SKB g)
    (hH : HeapIs g H) : H.toNat ≤ 33806089496 := by
  obtain ⟨⟨⟨_,_,⟨h',hh,lo,hi,al⟩,_⟩,_⟩,_⟩ := h
  unfold HeapIs at hH; rw [hh] at hH
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hH
  subst hH; exact hi

section cl
variable {SP0 P0 FM w : BitVec 64} {G0 : GA}
variable {D : BitVec 64 → Prop} {B : Bool}
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Ts Bs SKB J C Nj H0 : BitVec 64} {M0 : Mem}

/-- The tail of `clear_account_preserving_balance` (as `increment_nonce`, with the two stores). -/
theorem clearTailT_aqgd (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ lo : TLay, lo.hdr M0 (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (ECH : BitVec 64) (hECH : G0.lookup (ofString "empty_code_hash") = some (.val (.word ECH))) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0 M' G')
      clearTail := by
  unfold clearTail
  refine aqgd_conseq (P := fun L M G => ∃ l : Fin n → TLay,
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ RegPure n c T Out H0 l ∧
      RegMem n c T l M ∧ TCont D B M (T ko) (l ko) ∧ (∀ x, (l ko).arr x → x.toNat < H0.toNat) ∧ M = M0 ∧
      HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (aqgd_ex (fun l => ?_)) (fun L M G ⟨ha,⟨l,pure,mem,tc,ab⟩,hM,hH,hn⟩ => ⟨l,ha,pure,mem,tc,ab,hM,hH,hn⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  -- a = get_account(addr)
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      M = M0' ∧ G = G0')
    (RRe := fun _ M0' _ _ M' G' => (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
      ((Reg n c T Out H' M' ∧ H0.toNat ≤ H'.toNat) ∧
        ∀ x, GaKeep SP0 P0 FM K Pd NB Out (T ko) (l ko) x → M' x = M0' x)) ∧ JW SP0 P0 FM G0 J C G')
    (Pc := fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V)))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1, HeapIs G H1 ∧ P0.toNat ≤ H1.toNat ∧ H0.toNat ≤ H1.toNat ∧ RegT n c T Out H1 M D B ko ∧
        ∀ x, Out x → M x = M0 x)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_account_lookup (by simp) ?_ ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L0 M0' G0' ⟨_,pure,mem,_,ab,_,hH,hn⟩
    refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_account_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (accountRegT_aqmh n c T kA kB ko hAB hAo hBo Ts Bs hTs hBs hcA hcB Out hOut H0 p0 K Pd NB hK0 hPd0 hNB0
        safe (hOutSafe w hOut).1 hwP l pure M0' mem ab))))
      (keepsSkBuf_of_installed originalRuntimeCode_account_lookup (by decide))) ?_ (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h)
    intro L M G ⟨ha,hM,hG⟩
    subst hM hG
    exact ⟨hn,H0,hH,⟨ha,rfl,l,reg_of pure mem,pure.2.1,pure.2.2⟩,rfl⟩
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_account_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨A,hA⟩,pure,mem,tc,ab,hM,_⟩ ⟨⟨hn',H1,hH1,⟨reg,hle⟩,fr⟩,jw⟩ ok
    subst hM
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    have keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        M' x = M x := fun x hx => fr x (Or.inl ⟨hx,hkoWs (l ko) (mem ko).2 x hx⟩)
    exact ⟨⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,
      ⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩⟩,hn',H1,hH1,jw_heap jw hH1,hle,
      regT_of_reg l pure tc ab reg hle keepT,fun x hx => fr x (Or.inr ⟨hx,hOutSafe x hx⟩)⟩
  -- a = acct_copy(a)
  refine aqgd_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H0.toNat ≤ H1.toNat ∧ H1.toNat ≤ H2.toNat ∧ RegT n c T Out H1 M D B ko ∧ ∀ x, Out x → M x = M0 x)
    (aqgd_jws (aqgd_of_aqg (aqg_callAssign (Vn' := fun _ => True)
      (Pe := fun _ M0' G0' L M G => (∃ Aa : BitVec 64, L.lookup (ofString "a") = some (.val (.word Aa))) ∧
        M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' v M' G' => ∃ H1, HeapIs G0' H1 ∧ (v = .val (.word H1) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ ∀ x, x.toNat < H1.toNat → M' x = M0' x))
      _ _ _ _ _ _ originalRuntimeCode_acctCopy_lookup (by simp) ?_ ?_ ?_)) (by decide)) ?_
  · intro L0 M0' G0' ⟨_,hn,H1,hH1,_,_,reg,_⟩
    have hw1 : w.toNat < H1.toNat := by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 w hOut ko (Or.inr (Or.inr (by omega)))
    refine aqg_conseq (P := fun L M G => ∃ Aa, L.lookup (ofString "a") = some (.val (.word Aa)) ∧ M = M0' ∧
        HeapIs G H1 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (aqg_ex (fun Aa => acctCopy_aqg J C Aa H1 Nj M0' hw1)) ?_ (fun _ _ _ _ => trivial) (fun _ _ _ h => ⟨H1,hH1,h⟩)
    intro L M G ⟨⟨Aa,ha⟩,hM,hG⟩
    subst hM hG
    exact ⟨Aa,ha,rfl,hH1,hn⟩
  · intro F s values callee rs _ G hG ⟨⟨_,⟨V,hV⟩⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hV] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_acctCopy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨V,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨A,hA⟩,_⟩,_,H1,hH1,p1,h01,reg,fr⟩ ⟨H1',hH1',ev,hn',H',hH',hle,frc⟩
    have e : H1' = H1 := by unfold HeapIs at hH1 hH1'; rw [hH1] at hH1'; simpa using hH1'.symm
    subst e ev
    have ltOut : ∀ x, Out x → x.toNat < H1'.toNat := fun x hx => by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 x hx ko (Or.inr (Or.inr (by omega)))
    refine ⟨⟨_,rfl⟩,⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,hn',
      H1',H',by simp [HolFiniteMapExact.lookup_update,FUPDATE],hH',p1,h01,hle,
      regT_keep_below reg (fun x hx => frc x hx),fun x hx => (frc x (ltOut x hx)).trans (fr x hx)⟩
  -- st a + 0, 0; st a + 48, empty_code_hash: into the fresh copy
  refine aqgd_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H0.toNat ≤ H1.toNat ∧ H1.toNat ≤ H2.toNat ∧ RegT n c T Out H1 M D B ko ∧ ∀ x, Out x → M x = M0 x)
    (aqgd_store _ _ (fun s G _ hG ⟨ha,hn,H1,H2,hl,hH2,p1,h01,hle,reg,fr⟩ _ => ?_)
    (fun s x G _ _ _ _ ev => by simp [EV,evalHOLExact] at ev; exact ⟨_,ev.symm⟩)) ?_
  · unfold GIs at hG; subst hG
    have hw1 : w.toNat < H1.toNat := by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 w hOut ko (Or.inr (Or.inr (by omega)))
    have ltOut : ∀ x, Out x → x.toNat < H1.toNat := fun x hx => by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 x hx ko (Or.inr (Or.inr (by omega)))
    refine ⟨H1 + 0#64,by simp [EV,evalHOLExact,evalListHOLExact,hl,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun e => by simp at e; subst e; omega,fun y _ => ⟨ha,hn,H1,H2,hl,hH2,p1,h01,hle,
        regT_keep_below reg (fun x hx => ?_),fun x hx => ?_⟩⟩
    · have : x ≠ H1 + 0#64 := by simp; intro e; subst e; omega
      simp only [if_neg this]
    · have : x ≠ H1 + 0#64 := by have := ltOut x hx; simp; intro e; subst e; omega
      simp only [if_neg this]; exact fr x hx
  refine aqgd_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H0.toNat ≤ H1.toNat ∧ H1.toNat ≤ H2.toNat ∧ RegT n c T Out H1 M D B ko ∧ ∀ x, Out x → M x = M0 x)
    (aqgd_store _ _ (fun s G aw hG ⟨ha,hn,H1,H2,hl,hH2,p1,h01,hle,reg,fr⟩ _ => ?_)
    (fun s x G aw _ _ _ ev => by
      obtain ⟨eg,_⟩ := aw.1.1.2.2.2 (ofString "empty_code_hash") (by decide)
      simp [EV,evalHOLExact,eg,hECH] at ev; exact ⟨_,ev.symm⟩)) ?_
  · unfold GIs at hG; subst hG
    have hE := clr_heap_le aw hH2
    have e48 : (H1 + 48#64).toNat = H1.toNat + 48 := by rw [BitVec.toNat_add]; simp; omega
    have hw1 : w.toNat < H1.toNat := by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 w hOut ko (Or.inr (Or.inr (by omega)))
    have ltOut : ∀ x, Out x → x.toNat < H1.toNat := fun x hx => by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 x hx ko (Or.inr (Or.inr (by omega)))
    refine ⟨H1 + 48#64,by simp [EV,evalHOLExact,evalListHOLExact,hl,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun e => by rw [← e] at e48; omega,fun y _ => ⟨ha,hn,H1,H2,hl,hH2,p1,h01,hle,
        regT_keep_below reg (fun x hx => ?_),fun x hx => ?_⟩⟩
    · have : x ≠ H1 + 48#64 := fun e => by rw [← e] at e48; omega
      simp only [if_neg this]
    · have : x ≠ H1 + 48#64 := fun e => by have := ltOut x hx; rw [← e] at e48; omega
      simp only [if_neg this]; exact fr x hx
  -- modify_state_commit(addr, a)
  refine aqgd_seq (Q := fun _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0 M' G')
    (aqgd_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' _ L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧
        (∃ H2, RegT n c T Out H2 M D B ko ∧ HeapIs G H2 ∧ H0.toNat ≤ H2.toNat) ∧ M = M0' ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (RRe := fun _ M0' _ _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0' M' G')
      _ _ _ _ _ originalRuntimeCode_modifyStateCommit_lookup (by simp) ?_ ?_ ?_)
    (aqgd_return _ (fun _ _ _ _ _ h _ _ => h))
  · intro L0 M0' G0' _
    refine aqgd_conseq (P := fun L M G => ∃ H2 : BitVec 64, H0.toNat ≤ H2.toNat ∧
        ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧
        RegT n c T Out H2 M D B ko ∧ M = M0' ∧ HeapIs G H2 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))))
      (aqgd_ex (fun H2 => aqgd_conseq (P := fun L M G =>
          ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
          (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧
          RegT n c T Out H2 M D B ko ∧ M = M0' ∧ HeapIs G H2 ∧
          G.lookup (ofString "journal_n") = some (.val (.word Nj))) ∧ H0.toNat ≤ H2.toNat)
        (aqgd_purePre (fun h02 => aqgd_conseq (modifyStateCommitT_aqgd (H0 := H2) (Nj := Nj) (M0 := M0') ne ne16
          hTs hco hcd hc16 (by omega) jfit hwJ hwP hOut hwS hJO hSO jsep) (fun _ _ _ h => h) (fun _ _ _ h => h)
          (fun _ _ _ ⟨H',hH',hle',r,hn,fr⟩ => ⟨H',hH',by omega,r,hn,fr⟩)))
        (fun L M G ⟨h02,rest⟩ => ⟨rest,h02⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)))
      (fun L M G ⟨ha,hv,⟨H2,reg,hH2,h02⟩,hM,hn⟩ => ⟨H2,h02,ha,hv,reg,hM,hH2,hn⟩) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,hn,H1,H2,hl,hH2,_,h01,hle,reg,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA,hl] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_modifyStateCommit_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨H1,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨H2,regT_mono reg hle,hH2,by omega⟩,rfl,hn⟩
  · intro L M G v M' G' ⟨_,_,H1,H2,_,_,_,_,_,_,fr⟩ ⟨H',hH',hle',reg',hn',fr'⟩
    exact ⟨H',hH',hle',reg',hn',fun x hx hj hs => (fr' x hx hj hs).trans (fr x hx)⟩


#print axioms clearTailT_aqgd
/-- The actual `clear_account_preserving_balance(addr)` over the content-carrying registry. -/
theorem clearAcctPBT_aqgd (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (ECH : BitVec 64) (hECH : G0.lookup (ofString "empty_code_hash") = some (.val (.word ECH))) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0 M' G')
      (sourceFunctionBody Guest.guestFn_clear_account_preserving_balance) := by
  rw [source_clearAcctPB_body]
  -- destroy_storage(addr)
  refine aqgd_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      DSPost n c T Out ko D B J C SKB H0 Nj M0 M G)
    (aqgd_callSpec (Vn' := fun x => x ≠ ofString "m" ∧ x ≠ ofString "s")
      (Pe := fun _ M0' _ L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0' ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (RRe := fun _ M0' _ _ M' G' => DSPost n c T Out ko D B J C SKB H0 Nj M0' M' G')
      _ _ _ _ _ originalRuntimeCode_destroyStorage_lookup (by simp)
      (fun _ M0' _ _ => destroyStorage_aqgd (M0 := M0') ne hTs hco hcd p0 jfit hwJ hwP hOut hwS hJO hSO jsep)
      ?_ ?_) ?_
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,reg,_,hH,hn⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,hA] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_destroyStorage_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,reg,rfl,hH,hn⟩
  · intro L M G v M' G' ⟨ha,_,hM,_,_⟩ post
    subst hM
    exact ⟨ha,post⟩
  -- the tail from the state after destroy_storage
  refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × BitVec 64 × Mem,
      (((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegT n c T Out q.1 M D B ko ∧ M = q.2.2 ∧ HeapIs G q.1 ∧
        G.lookup (ofString "journal_n") = some (.val (.word q.2.1))) ∧
      (H0.toNat ≤ q.1.toNat ∧ ∀ x, Out x → ¬ InJ J C x → ¬ SkWin SKB x → q.2.2 x = M0 x)))
    (aqgd_ex (fun q => aqgd_purePre (fun ⟨h01,fr⟩ => aqgd_conseq
      (clearTailT_aqgd (H0 := q.1) (Nj := q.2.1) (M0 := q.2.2) ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16
        (by omega) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe (hkoWs q.2.2) ECH hECH)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ M' G' ⟨H',hH',hle,reg',hn',fr'⟩ => ⟨H',hH',by omega,reg',hn',
        fun x hx hj hs => (fr' x hx hj hs).trans (fr x hx hj hs)⟩))))
    (fun L M G ⟨ha,H,hH,hle,reg,hn,fr⟩ => by
      rcases hn with hn | ⟨_,hn⟩
      · exact ⟨(H,Nj,M),⟨ha,reg,rfl,hH,hn⟩,hle,fr⟩
      · exact ⟨(H,Nj + 1,M),⟨ha,reg,rfl,hH,hn⟩,hle,fr⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms clearAcctPBT_aqgd
end cl
end InitECandidate.Runtime
