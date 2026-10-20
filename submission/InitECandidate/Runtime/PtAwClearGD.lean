import InitECandidate.Runtime.PtAwCreateGD
import InitECandidate.Runtime.PtClearGD
/-!
The actual `clear_account_preserving_balance(addr)` keeps the accounts-written table ready (`AwPost`):
`destroy_storage`, `get_account`, the fresh copy and the two stores run over the registry restricted to the other
tables, with the table's cell and region among its outside words (kept); `modify_state_commit` keeps the table ready.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section cl2
variable {SP0 P0 FM w : BitVec 64} {G0 : GA}
variable {D : BitVec 64 → Prop} {B : Bool}
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Ts Bs SKB J C Nj H0 : BitVec 64} {M0 : Mem}
  {Bo U Sc : BitVec 64}

/-- The tail of `clear_account_preserving_balance` keeps the accounts-written table ready. -/
theorem clearTail_rv_aqgd (O0 : BitVec 64 → Prop) (Taw A0 Hl : BitVec 64) (la : TLay)
    (hOutEq : Out = fun x => O0 x ∨ AwFp Ts Taw la x)
    (aw : AwIL n c T ko O0 D B J C SKB Ts Taw Set.univ la Hl H0 M0)
    (hOut0 : O0 w) (hK : A0.toNat % 8 = 0) (hKE : A0.toNat + 52 ≤ 33806089496)
    (jB : J.toNat + C.toNat * 32 ≤ P0.toNat) (outB : ∀ x, O0 x → x.toNat < P0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (ne : kd ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
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
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => True)
      (fun L M G => L.lookup (ofString "addr") = some (.val (.word A0)) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => AwPost n c T ko O0 D B J C SKB Ts Taw Set.univ H0 M' G')
      clearTail := by
  unfold clearTail
  refine aqgd_conseq (P := fun L M G => ∃ l : Fin n → TLay,
      L.lookup (ofString "addr") = some (.val (.word A0)) ∧ RegPure n c T Out H0 l ∧
      RegMem n c T l M ∧ TCont D B M (T ko) (l ko) ∧ (∀ x, (l ko).arr x → x.toNat < H0.toNat) ∧ M = M0 ∧
      HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (aqgd_ex (fun l => ?_)) (fun L M G ⟨ha,⟨l,pure,mem,tc,ab⟩,hM,hH,hn⟩ => ⟨l,ha,pure,mem,tc,ab,hM,hH,hn⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  -- a = get_account(addr)
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => L.lookup (ofString "addr") = some (.val (.word A0)) ∧
      M = M0' ∧ G = G0')
    (RRe := fun _ M0' _ _ M' G' => (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
      ((Reg n c T Out H' M' ∧ H0.toNat ≤ H'.toNat) ∧
        ∀ x, GaKeep SP0 P0 FM K Pd NB Out (T ko) (l ko) x → M' x = M0' x)) ∧ JW SP0 P0 FM G0 J C G')
    (Pc := fun L M G => (L.lookup (ofString "addr") = some (.val (.word A0)) ∧
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V)))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1, HeapIs G H1 ∧ P0.toNat ≤ H1.toNat ∧ H0.toNat ≤ H1.toNat ∧ RegT n c T Out H1 M D B ko ∧
        ∀ x, Out x → M x = M0 x)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_account_lookup (by simp) ?_ ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L0 M0' G0' ⟨_,pure,mem,_,ab,_,hH,hn⟩
    refine aqgd_conseq (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_jws (aqgd_of_aqg (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_account_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (accountRegT_aqmh n c T kA kB ko hAB hAo hBo Ts Bs hTs hBs hcA hcB Out hOut H0 p0 K Pd NB hK0 hPd0 hNB0
        safe (hOutSafe w hOut).1 hwP l pure M0' mem ab))))
      (keepsSkBuf_of_installed originalRuntimeCode_account_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_account_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_account_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_account_lookup (by decide))) ?_ (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h)
    intro L M G ⟨ha,hM,hG⟩
    subst hM hG
    exact ⟨hn,H0,hH,⟨⟨A0,ha⟩,rfl,l,reg_of pure mem,pure.2.1,pure.2.2⟩,rfl⟩
  · intro F s values callee rs _ G hG ⟨hA,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_account_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨hA,pure,mem,tc,ab,hM,_⟩ ⟨⟨hn',H1,hH1,⟨reg,hle⟩,fr⟩,jw⟩ ok
    subst hM
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    have keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        M' x = M x := fun x hx => fr x (Or.inl ⟨hx,hkoWs (l ko) (mem ko).2 x hx⟩)
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA],
      ⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩⟩,hn',H1,hH1,jw_heap jw hH1,hle,
      regT_of_reg l pure tc ab reg hle keepT,fun x hx => fr x (Or.inr ⟨hx,hOutSafe x hx⟩)⟩
  -- a = acct_copy(a)
  refine aqgd_seq (Q := fun L M G => L.lookup (ofString "addr") = some (.val (.word A0)) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H0.toNat ≤ H1.toNat ∧ H1.toNat ≤ H2.toNat ∧ RegT n c T Out H1 M D B ko ∧ ∀ x, Out x → M x = M0 x)
    (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_jws (aqgd_of_aqg (aqg_callAssign (Vn' := fun _ => True)
      (Pe := fun _ M0' G0' L M G => (∃ Aa : BitVec 64, L.lookup (ofString "a") = some (.val (.word Aa))) ∧
        M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' v M' G' => ∃ H1, HeapIs G0' H1 ∧ (v = .val (.word H1) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ ∀ x, x.toNat < H1.toNat → M' x = M0' x))
      _ _ _ _ _ _ originalRuntimeCode_acctCopy_lookup (by simp) ?_ ?_ ?_)) (by decide)) (by decide) (by decide)
      (by decide)) ?_
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
  · intro L M G v M' G' ⟨⟨hA,_⟩,_,H1,hH1,p1,h01,reg,fr⟩ ⟨H1',hH1',ev,hn',H',hH',hle,frc⟩
    have e : H1' = H1 := by unfold HeapIs at hH1 hH1'; rw [hH1] at hH1'; simpa using hH1'.symm
    subst e ev
    have ltOut : ∀ x, Out x → x.toNat < H1'.toNat := fun x hx => by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 x hx ko (Or.inr (Or.inr (by omega)))
    refine ⟨⟨_,rfl⟩,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA],hn',
      H1',H',by simp [HolFiniteMapExact.lookup_update,FUPDATE],hH',p1,h01,hle,
      regT_keep_below reg (fun x hx => frc x hx),fun x hx => (frc x (ltOut x hx)).trans (fr x hx)⟩
  -- st a + 0, 0; st a + 48, empty_code_hash: into the fresh copy
  refine aqgd_seq (Q := fun L M G => L.lookup (ofString "addr") = some (.val (.word A0)) ∧
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
  refine aqgd_seq (Q := fun L M G => L.lookup (ofString "addr") = some (.val (.word A0)) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H0.toNat ≤ H1.toNat ∧ H1.toNat ≤ H2.toNat ∧ RegT n c T Out H1 M D B ko ∧ ∀ x, Out x → M x = M0 x)
    (aqgd_store _ _ (fun s G aw hG ⟨ha,hn,H1,H2,hl,hH2,p1,h01,hle,reg,fr⟩ _ => ?_)
    (fun s x G aw _ _ _ ev => by
      obtain ⟨eg,_⟩ := aw.1.1.1.1.1.2.2.2 (ofString "empty_code_hash") (by decide)
      simp [EV,evalHOLExact,eg,hECH] at ev; exact ⟨_,ev.symm⟩)) ?_
  · unfold GIs at hG; subst hG
    have hE := clr_heap_le aw.1.1.1 hH2
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
  -- modify_state_commit(addr, a): the table, framed so far, stays ready
  have hwH0 : w.toNat < H0.toNat := by omega
  refine aqgd_seq (Q := fun _ M' G' => AwPost n c T ko O0 D B J C SKB Ts Taw Set.univ H0 M' G')
    ?_ (aqgd_return _ (fun _ _ _ _ hG h _ _ => by unfold GIs at hG; subst hG; exact h))
  refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × BitVec 64, (L.lookup (ofString "addr") =
      some (.val (.word A0)) ∧ L.lookup (ofString "a") = some (.val (.word q.1))) ∧
      (G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ HeapIs G q.2 ∧ P0.toNat ≤ q.2.toNat ∧
        H0.toNat ≤ q.2.toNat ∧ RegT n c T Out q.2 M D B ko ∧ ∀ x, Out x → M x = M0 x))
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨ha,hn,H1,H2,hl,hH2,p1,h01,hle,reg,fr⟩ =>
      ⟨(H1,H2),⟨ha,hl⟩,hn,hH2,Nat.le_trans p1 hle,Nat.le_trans h01 hle,regT_mono reg hle,fr⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨V,H2⟩
  dsimp only
  refine aqgd_ghostJ (fun M2 G2 ⟨hn,hH2,p2,h02,reg2,fr2⟩ => ?_)
  rw [hOutEq] at reg2 fr2
  have aw2 := awIL_frame aw reg2 h02 (fun x hx _ _ => fr2 x hx)
  refine aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' _ L M G => (L.lookup (ofString "addr") = some (.val (.word A0)) ∧
      L.lookup (ofString "a") = some (.val (.word V))) ∧ (M = M0' ∧ HeapIs G H2 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj))))
    (RRe := fun _ _ _ _ M' G' => AwPost n c T ko O0 D B J C SKB Ts Taw Set.univ H2 M' G')
    _ _ _ _ _ originalRuntimeCode_modifyStateCommit_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,_⟩
    subst hM
    exact msc_rv_aqgd Ts Taw A0 V Nj H2 Hl la M0' ne hTs hco hcd aw2 p2 jfit hwJ hwP hOut0 hwS
      (fun x hx => by have := hJO x hx; rw [hOutEq] at this; rcases this with h | h
                      · exact h
                      · exact absurd hx (aw.2.2.1 x h).2.1)
      (fun x hx => by
        obtain ⟨ho,hc⟩ := hSO x hx
        rw [hOutEq] at ho
        rcases ho with h | h
        · exact ⟨h,hc⟩
        · exact absurd hx (aw.2.2.1 x h).2.2.1) jsep jB outB Dall trivial trivial hK hKE
  · intro F s values callee rs _ G hG ⟨⟨ha,hv⟩,_,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ha,hv] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_modifyStateCommit_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,by rw [hG1]; exact hH2,
      by rw [hG1]; exact hn⟩
  · intro L M G v M' G' _ post
    exact awPost_mono post h02

#print axioms clearTail_rv_aqgd

/-- `clear_account_preserving_balance` keeps the accounts-written table ready. -/
theorem clearAcct_rv_aqgd (O0 : BitVec 64 → Prop) (Taw A0 Hl : BitVec 64) (la : TLay)
    (hOutEq : Out = fun x => O0 x ∨ AwFp Ts Taw la x)
    (aw : AwIL n c T ko O0 D B J C SKB Ts Taw Set.univ la Hl H0 M0)
    (hOut0 : O0 w) (hK : A0.toNat % 8 = 0) (hKE : A0.toNat + 52 ≤ 33806089496)
    (jB : J.toNat + C.toNat * 32 ≤ P0.toNat) (outB : ∀ x, O0 x → x.toNat < P0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (ne : kd ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
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
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => True)
      (fun L M G => L.lookup (ofString "addr") = some (.val (.word A0)) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => AwPost n c T ko O0 D B J C SKB Ts Taw Set.univ H0 M' G')
      (sourceFunctionBody Guest.guestFn_clear_account_preserving_balance) := by
  rw [source_clearAcctPB_body]
  -- destroy_storage(addr)
  refine aqgd_seq (Q := fun L M G => L.lookup (ofString "addr") = some (.val (.word A0)) ∧
      DSPost n c T Out ko D B J C SKB H0 Nj M0 M G)
    (aqgd_callSpec (Vn' := fun x => x ≠ ofString "m" ∧ x ≠ ofString "s")
      (Pe := fun _ M0' _ L M G => L.lookup (ofString "addr") = some (.val (.word A0)) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0' ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (RRe := fun _ M0' _ _ M' G' => DSPost n c T Out ko D B J C SKB H0 Nj M0' M' G')
      _ _ _ _ _ originalRuntimeCode_destroyStorage_lookup (by simp)
      (fun _ M0' _ _ => aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc)
        (aqgd_conseq (destroyStorage_aqgd (M0 := M0') ne hTs hco hcd p0 jfit hwJ hwP hOut hwS hJO hSO jsep)
          (fun L M G ⟨ha,r⟩ => ⟨⟨A0,ha⟩,r⟩) (fun _ _ _ h => h) (fun _ _ _ h => h))
        (keepsBo_of_installed originalRuntimeCode_destroyStorage_lookup (by decide))
        (keepsWs_of_installed originalRuntimeCode_destroyStorage_lookup (by decide))
        (keepsScr_of_installed originalRuntimeCode_destroyStorage_lookup (by decide)))
      ?_ ?_) ?_
  · intro F s values callee rs _ G hG ⟨hA,reg,_,hH,hn⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,hA] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_destroyStorage_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],reg,rfl,hH,hn⟩
  · intro L M G v M' G' ⟨ha,_,hM,_,_⟩ post
    subst hM
    exact ⟨ha,post⟩
  -- the tail from the state after destroy_storage
  refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × BitVec 64 × Mem,
      ((L.lookup (ofString "addr") = some (.val (.word A0)) ∧
        RegT n c T Out q.1 M D B ko ∧ M = q.2.2 ∧ HeapIs G q.1 ∧
        G.lookup (ofString "journal_n") = some (.val (.word q.2.1))) ∧
      (H0.toNat ≤ q.1.toNat ∧ (∀ x, Out x → ¬ InJ J C x → ¬ SkWin SKB x → q.2.2 x = M0 x) ∧
        RegT n c T Out q.1 q.2.2 D B ko)))
    (aqgd_ex (fun q => aqgd_purePre (fun ⟨h01,fr,reg1⟩ => aqgd_conseq
      (clearTail_rv_aqgd (H0 := q.1) (Nj := q.2.1) (M0 := q.2.2) O0 Taw A0 Hl la hOutEq
        (awIL_frame aw (by rw [hOutEq] at reg1; exact reg1) h01 (fun x hx hj hs => by
          have := fr x (by rw [hOutEq]; exact hx) hj hs; exact this))
        hOut0 hK hKE jB outB Dall ne hAB hAo hBo hTs hBs hcA hcB hco hcd
        (by omega) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe (hkoWs q.2.2) ECH hECH)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ M' G' post => awPost_mono post h01))))
    (fun L M G ⟨ha,H,hH,hle,reg,hn,fr⟩ => by
      rcases hn with hn | ⟨_,hn⟩
      · exact ⟨(H,Nj,M),⟨ha,reg,rfl,hH,hn⟩,hle,fr,reg⟩
      · exact ⟨(H,Nj + 1,M),⟨ha,reg,rfl,hH,hn⟩,hle,fr,reg⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms clearAcct_rv_aqgd
end cl2
end InitECandidate.Runtime
