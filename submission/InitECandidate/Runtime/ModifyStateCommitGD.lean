import InitECandidate.Runtime.DestroyAccountGD
/-!
Original `modify_state_commit(addr, a)` in the fixed-domain triple over the content-carrying registry `RegT`:
`set_account` (fine frame, `regT_after_setAccount`), the read-only `acct_is_empty`, and for an empty account the
original `destroy_account` through `destroyAccount_aqgd`, so no destroy contract is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA} {D : BitVec 64 → Prop} {B : Bool}

/-- Registry with content after `set_account` (`setAccountF_aqg`'s post) on account table `kA ≠ ko`. -/
theorem regT_after_setAccount {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA : Fin n}
    {J C H1 H' : BitVec 64} {M M' : Mem} (neA : kA ≠ ko) (l : Fin n → TLay) (pure : RegPure n c T Out H1 l)
    (tc : TCont D B M (T ko) (l ko)) (ab : ∀ x, (l ko).arr x → x.toNat < H1.toNat)
    (hJO : ∀ x, InJ J C x → Out x) (reg : Reg n c T Out H' M') (hle : H1.toNat ≤ H'.toNat)
    (fr : ∀ x, x.toNat < H1.toNat → ¬ InJ J C x → ¬ (l kA).canon (T kA) H1 x → M' x = M x) :
    RegT n c T Out H' M' D B ko ∧ ∀ x, Out x → ¬ InJ J C x → M' x = M x := by
  have lay := (pure.1 ko).1
  have ltH : ∀ x, Out x → x.toNat < H1.toNat := fun x ho => by
    by_contra h; exact pure.2.2 x ho ko (Or.inr (Or.inr (by omega)))
  refine ⟨regT_of_reg l pure tc ab reg hle (fun x hx => ?_),fun x ho hj => fr x (ltH x ho) hj (pure.2.2 x ho kA)⟩
  refine fr x ?_ (fun hj => pure.2.2 x (hJO x hj) ko (intabf_canon hx)) (pure.2.1 kA ko neA x ?_)
  · rcases hx with hh | ha
    · have := lay.hdrP; omega
    · exact ab x ha
  · rcases hx with hh | ha
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr ha)

#print axioms regT_after_setAccount

section mc
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA : Fin n}
  {Ts SKB J C Nj H0 : BitVec 64} {M0 : Mem}

/-- State after `set_account` inside `modify_state_commit`. -/
def MSX (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (J C H0 : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ H1 : BitVec 64, HeapIs G H1 ∧ H0.toNat ≤ H1.toNat ∧ RegT n c T Out H1 M D B ko ∧
    (∃ Nj' : BitVec 64, G.lookup (ofString "journal_n") = some (.val (.word Nj'))) ∧
    ∀ x, Out x → ¬ InJ J C x → M x = M0 x

set_option maxHeartbeats 16000000 in
/-- The original `modify_state_commit(addr, a)` over the content-carrying registry: `set_account`, the read-only
`acct_is_empty`, and for an empty account the original `destroy_account` (no destroy contract assumed). -/
theorem modifyStateCommitT_aqgd (ne : kd ≠ ko) (neA : kA ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64) (hcA : c kA = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0 M' G')
      (sourceFunctionBody Guest.guestFn_modify_state_commit) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_modify_state_commit,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  -- set_account(addr, a) on fixed layouts
  refine aqgd_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ MSX n c T Out ko D B J C H0 M0 M G)
    (aqgd_conseq (P := fun L M G => ∃ l : Fin n → TLay,
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ RegPure n c T Out H0 l ∧
      RegMem n c T l M ∧ TCont D B M (T ko) (l ko) ∧ (∀ x, (l ko).arr x → x.toNat < H0.toNat) ∧ M = M0 ∧
      HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (aqgd_ex (fun l => ?_)) (fun L M G ⟨ha,hv,⟨l,pure,mem,tc,ab⟩,hM,hH,hn⟩ => ⟨l,ha,hv,pure,mem,tc,ab,hM,hH,hn⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)) ?_
  · refine aqgd_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' _ L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ M = M0' ∧
        HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (RRe := fun _ M0' _ _ M' G' => Nj.toNat < C.toNat ∧
        G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
        ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
          ∀ x, x.toNat < H0.toNat → ¬ InJ J C x → ¬ (l kA).canon (T kA) H0 x → M' x = M0' x)
      _ _ _ _ _ originalRuntimeCode_setAccount_lookup (by simp) ?_ ?_ ?_
    · intro L0 M0' G0' ⟨_,_,pure,mem,_,_,_,_,_⟩
      exact aqgd_jws (aqgd_of_aqg (setAccountF_aqg n c T Out l kA Ts hTs hcA J C Nj H0 pure M0' mem p0 jfit
        hwJ hwP hOut jsep)) (keepsSkBuf_of_installed originalRuntimeCode_setAccount_lookup (by decide))
    · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,⟨V,hV⟩,_,_,_,_,_,hH,hn⟩ _ args lookup
      unfold GIs at hG; subst hG
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hA,hV] at args
      subst args
      rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_setAccount_lookup] at lookup
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      obtain ⟨_,rfl,_⟩ := lookup
      exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
        ⟨V,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,hH,hn⟩
    · intro L M G v M' G' ⟨ha,hv,pure,_,tc,ab,hM,_,_⟩ ⟨_,hn',H',hH',hle,reg,fr⟩
      subst hM
      obtain ⟨regT,frO⟩ := regT_after_setAccount neA l pure tc ab hJO reg hle fr
      exact ⟨ha,hv,H',hH',hle,regT,⟨_,hn'⟩,frO⟩
  -- e = acct_is_empty(a): read-only
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      MSX n c T Out ko D B J C H0 M0 M G) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_acctIsEmpty_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf acctIsEmpty_mf (by body_check Guest.guestFn_acct_is_empty)
      (by body_check Guest.guestFn_acct_is_empty) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨A,hA⟩,_,wp⟩ ⟨e1,e2⟩ _
    subst e1 e2
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,wp⟩
  -- an empty account is destroyed
  refine aqgd_seq (Q := fun _ M G => DAPost n c T Out ko D B J C SKB H0 M0 M G)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ ⟨⟨_,H1,hH1,hle,reg,hn,fr⟩,_⟩ =>
        ⟨H1,hH1,hle,reg,hn,fun x ho hj _ => fr x ho hj⟩) (fun _ _ _ h => h)))
    (aqgd_return _ (fun _ _ _ _ _ h _ _ => h))
  refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × BitVec 64,
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ HeapIs G q.1 ∧ H0.toNat ≤ q.1.toNat ∧
      RegT n c T Out q.1 M D B ko ∧ G.lookup (ofString "journal_n") = some (.val (.word q.2)) ∧
      ∀ x, Out x → ¬ InJ J C x → M x = M0 x)
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨⟨ha,H1,hH1,hle,reg,⟨Nj',hn⟩,fr⟩,_⟩ => ⟨(H1,Nj'),ha,hH1,hle,reg,hn,fr⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨H1,Nj'⟩
  dsimp only
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' _ L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      RegT n c T Out H1 M D B ko ∧ M = M0' ∧ HeapIs G H1 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj')))
    (RRe := fun _ M0' _ _ M' G' => DAPost n c T Out ko D B J C SKB H1 M0' M' G')
    _ _ _ _ _ originalRuntimeCode_destroyAccount_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,_,hle,_,_,_⟩
    exact destroyAccount_aqgd (M0 := M0') ne neA hTs hco hcd hcA (by omega) jfit hwJ hwP hOut hwS hJO hSO jsep
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,hH,_,reg,hn,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_destroyAccount_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,reg,rfl,hH,hn⟩
  · intro L M G v M' G' ⟨_,_,hle,_,_,fr⟩ ⟨H',hH',hle',reg',hn',fr'⟩
    exact ⟨H',hH',le_trans hle hle',reg',hn',fun x ho hj hs => (fr' x ho hj hs).trans (fr x ho hj)⟩

#print axioms modifyStateCommitT_aqgd
end mc
end InitECandidate.Runtime
