import InitECandidate.Runtime.PtSegAllGD
import InitECandidate.Runtime.OriginalPtSufCode
/-!
The actual `create_ether(addr, amount)` over the content-carrying registry (`get_account`, `acct_copy`,
`u256_add` (memory frame), four-word balance store into the fresh copy, `modify_state_commit`), its callee entry,
and the call site keeping `PXR` over the scratch-pinned process arena.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : GA} {D : BitVec 64 → Prop} {B : Bool}

/-- Local `nb` holds four words. -/
def NbL (L : GA) : Prop :=
  ∃ b0 b1 b2 b3 : BitVec 64,
    L.lookup (ofString "nb") = some (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)])

def ceBody : ProgHOL 64 :=
  (.decCall (ofString "a") .one (ofString "get_account") [(.var .local (ofString "addr"))] (.seq (.call (some ((some (.local,ofString "a")),none)) (ofString "acct_copy") [(.var .local (ofString "a"))]) (.decCall (ofString "nb") (.comb [.one,.one,.one,.one]) (ofString "u256_add") [(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "a")),(.const 8)])),(.var .local (ofString "amount"))] (.seq (.store (.op .add [(.var .local (ofString "a")),(.const 8)]) (.var .local (ofString "nb"))) (.seq (.call (some (none,none)) (ofString "modify_state_commit") [(.var .local (ofString "addr")),(.var .local (ofString "a"))]) (.return (.const 0)))))))

theorem ceBody_eq : sourceFunctionBody Guest.guestFn_create_ether = ceBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_create_ether,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl



section ce
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Ts Bs SKB J C Nj H0 : BitVec 64} {M0 : Mem}

/-- The original `create_ether(addr, amount)` over the content-carrying registry: `get_account`, a fresh copy,
`nb = u256_add(balance, amount)` (memory frame), the four-word store of `nb` into the copy, and the original
`modify_state_commit` (no destroy contract). -/
theorem createEtherT_aqgd (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
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
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun x => x ≠ ofString "amount" ∧ x ≠ ofString "nb")
      (fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0 M' G')
      (sourceFunctionBody Guest.guestFn_create_ether) := by
  rw [ceBody_eq]; unfold ceBody
  refine aqgd_conseq (P := fun L M G => ∃ l : Fin n → TLay,
      ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧ RegPure n c T Out H0 l ∧
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
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ AmtL L) ∧
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
    intro L M G ⟨⟨A,hA⟩,hM,hG⟩
    subst hM hG
    exact ⟨hn,H0,hH,⟨⟨A,hA⟩,rfl,l,reg_of pure mem,pure.2.1,pure.2.2⟩,rfl⟩
  · intro F s values callee rs _ G hG ⟨⟨⟨A,hA⟩,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_account_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨A,hA⟩,am⟩,pure,mem,tc,ab,hM,_⟩ ⟨⟨hn',H1,hH1,⟨reg,hle⟩,fr⟩,jw⟩ ok
    subst hM
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    have keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        M' x = M x := fun x hx => fr x (Or.inl ⟨hx,hkoWs (l ko) (mem ko).2 x hx⟩)
    exact ⟨⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,
      ⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,amtL_update am _⟩,hn',H1,hH1,jw_heap jw hH1,hle,
      regT_of_reg l pure tc ab reg hle keepT,fun x hx => fr x (Or.inr ⟨hx,hOutSafe x hx⟩)⟩
  -- a = acct_copy(a)
  refine aqgd_seq (Q := fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧
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
  · intro F s values callee rs _ G hG ⟨⟨_,⟨V,hV⟩,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hV] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_acctCopy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨V,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨A,hA⟩,_,am⟩,_,H1,hH1,p1,h01,reg,fr⟩ ⟨H1',hH1',ev,hn',H',hH',hle,frc⟩
    have e : H1' = H1 := by unfold HeapIs at hH1 hH1'; rw [hH1] at hH1'; simpa using hH1'.symm
    subst e ev
    have ltOut : ∀ x, Out x → x.toNat < H1'.toNat := fun x hx => by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 x hx ko (Or.inr (Or.inr (by omega)))
    refine ⟨⟨_,rfl⟩,⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,
      amtL_update am _⟩,hn',
      H1',H',by simp [HolFiniteMapExact.lookup_update,FUPDATE],hH',p1,h01,hle,
      regT_keep_below reg (fun x hx => frc x hx),fun x hx => (frc x (ltOut x hx)).trans (fr x hx)⟩
  -- nb = u256_add(lds (a + 8), amount)
  refine aqgd_decCallSpecS (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ NbL L) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H0.toNat ≤ H1.toNat ∧ H1.toNat ≤ H2.toNat ∧ RegT n c T Out H1 M D B ko ∧ ∀ x, Out x → M x = M0 x)
    (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_u256Add_lookup (fun _ _ _ _ _ h => h.elim)
    (fun _ M0' G0' _ => aqgd_of_mf mf_u256_add (by body_check Guest.guestFn_u256_add)
      (by body_check Guest.guestFn_u256_add) M0' G0') (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => absurd rfl h.2) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨⟨A,hA⟩,_⟩,hn,H1,H2,hl,rest⟩ ⟨eM,eG⟩ ok
    subst eM eG
    obtain ⟨b0,b1,b2,b3,rfl⟩ := u4v_of_shape ((shapeEqHOL_eq_true _ _).mp ok)
    exact ⟨⟨⟨A,by rw [lookup_update_ne' _ _ (by decide)]; exact hA⟩,b0,b1,b2,b3,lookup_update_eq' _ _ _⟩,hn,H1,H2,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hl,rest⟩
  -- st a + 8, nb: four words into the fresh copy
  refine aqgd_seq (Q := fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ NbL L) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H0.toNat ≤ H1.toNat ∧ H1.toNat ≤ H2.toNat ∧ RegT n c T Out H1 M D B ko ∧ ∀ x, Out x → M x = M0 x)
    (aqgd_jws (aqgd_of_aqg (aqg_store4 _ _
      (fun s G aw hG ⟨⟨ha,⟨b0,b1,b2,b3,hb⟩⟩,hn,H1,H2,hl,hH2,p1,h01,hle,reg,fr⟩ _ => ?_))) (by decide)) ?_
  · unfold GIs at hG; subst hG
    have ltOut : ∀ x, Out x → x.toNat < H1.toNat := fun x hx => by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 x hx ko (Or.inr (Or.inr (by omega)))
    have hw1 := ltOut w hOut
    have hi := jw_heap_hi aw hH2
    have e : ∀ k : BitVec 64, k.toNat < 40 → (H1 + 8#64 + k).toNat = H1.toNat + 8 + k.toNat := fun k hk => by
      rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega),
        BitVec.toNat_add_of_lt (by simp; omega)]; simp
    have e0 : (H1 + 8#64).toNat = H1.toNat + 8 := by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
    have low : ∀ x, x.toNat < H1.toNat → x ≠ H1 + 8#64 ∧ x ≠ H1 + 8#64 + 8#64 ∧ x ≠ H1 + 8#64 + 16#64 ∧
        x ≠ H1 + 8#64 + 24#64 := fun x hx =>
      ⟨fun h => by subst h; rw [e0] at hx; omega,fun h => by subst h; rw [e _ (by decide)] at hx; simp at hx; omega,
        fun h => by subst h; rw [e _ (by decide)] at hx; simp at hx; omega,
        fun h => by subst h; rw [e _ (by decide)] at hx; simp at hx; omega⟩
    obtain ⟨l0,l8,l16,l24⟩ := low w hw1
    refine ⟨H1 + 8#64,b0,b1,b2,b3,
      by simp [EV,evalHOLExact,evalListHOLExact,hl,wordOpHOL,wordOp,valueIsWord,valueWord],
      by simp [EV,evalHOLExact,hb],l0,l8,l16,l24,fun M' hM' => ⟨⟨ha,b0,b1,b2,b3,hb⟩,hn,H1,H2,hl,hH2,p1,h01,hle,
        regT_keep_below reg (fun x hx => ?_),fun x hx => ?_⟩⟩
    · obtain ⟨a0,a8,a16,a24⟩ := low x hx
      exact hM' x a0 a8 a16 a24
    · obtain ⟨a0,a8,a16,a24⟩ := low x (ltOut x hx)
      exact (hM' x a0 a8 a16 a24).trans (fr x hx)
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
  · intro F s values callee rs _ G hG ⟨⟨⟨A,hA⟩,_⟩,hn,H1,H2,hl,hH2,_,h01,hle,reg,_⟩ _ args lookup
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

#print axioms createEtherT_aqgd
end ce

theorem ce_callee {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "create_ether") values = some (body,callee,rs)) :
    SL (fun x => x ≠ ofString "amount" ∧ x ≠ ofString "nb") callee ∧ AmtL callee ∧
      ∃ A : BitVec 64, callee.lookup (ofString "addr") = some (.val (.word A)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i b0 cl rs0 found
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨_,hc,_⟩ := h
    have hl : callee.lookup = cl := by rw [← hc]
    clear hc
    unfold Flapjack.lookupCodeHOLExact at found
    rw [originalRuntimeCode_createEther_lookup] at found
    generalize sourceFunctionBody Guest.guestFn_create_ether = BB at found
    dsimp only at found
    split at found
    · rename_i cond
      obtain ⟨_,hlen,hall⟩ := cond
      simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨_,hcl,_⟩ := found
      match values, hlen, hall with
      | [v0,v1], _, hall =>
        simp only [List.zip_cons_cons,List.zip_nil_right,List.all_cons,List.all_nil,Bool.and_true,
          Bool.and_eq_true] at hall
        obtain ⟨s0,s1⟩ := hall
        obtain ⟨a,rfl⟩ : ∃ a : BitVec 64, v0 = .val (.word a) := scalar_of_shape s0
        obtain ⟨b0,b1,b2,b3,rfl⟩ := shape4' s1
        subst hcl
        have ne : ofString "addr" ≠ ofString "amount" := by decide
        refine ⟨fun x hx v hv => ?_,⟨b0,b1,b2,b3,?_⟩,a,?_⟩
        · rw [hl] at hv
          simp [List.map_cons,List.zip_cons_cons,hx.1] at hv
          exact ⟨a,hv.2.symm⟩
        · rw [hl]; simp
        · rw [hl]; simp [ne]
    · cases found

#print axioms ce_callee

section cs
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Excl : BitVec 64 → Prop} {Ts Bs SKB J C H0 Bo U Sc : BitVec 64} {M0 : Mem} {RR : ValueHOL 64 → Mem → GA → Prop}

theorem aqgd_call_createEtherS {LP : GA → Prop} (e1 e2 : ExpHOL 64) (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
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
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR
      (.call (some (none,none)) (ofString "create_ether") [e1,e2]) := by
  refine aqgd_callSpecS (Vn' := fun x => x ≠ ofString "amount" ∧ x ≠ ofString "nb")
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1, HeapIs G0' H1 ∧ DAPost n c T Out ko D B J C SKB H1 M0' M' G')
    _ _ _ _ _ originalRuntimeCode_createEther_lookup (fun _ _ _ h => (ce_callee h).1) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,h01,reg,hn,_⟩
    refine aqgd_conseq (aqgd_jwsbus (createEtherT_aqgd (H0 := H1) (M0 := M0') (Nj := Nj) ne ne16 hAB hAo hBo hTs
      hBs hcA hcB hco hcd hc16 (le_trans p0 h01) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe
      hOutSafe (hkoWs M0')) (keepsBo_of_installed originalRuntimeCode_createEther_lookup (by decide)) (keepsWs_of_installed originalRuntimeCode_createEther_lookup (by decide)) (keepsScr_of_installed originalRuntimeCode_createEther_lookup (by decide)))
      ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨ha,reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro F s values callee rs _ H _ _ _ _ lookup
    exact ⟨⟨(ce_callee lookup).2.2,(ce_callee lookup).2.1⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,h01,_,_,fr⟩ ⟨H1',hH',post⟩
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨lp,pxr_of_dapost hJE hSE h01 fr post⟩

#print axioms aqgd_call_createEtherS
end cs
end InitECandidate.Runtime
