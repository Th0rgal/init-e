import InitECandidate.Runtime.PtAwClearGD
import InitECandidate.Runtime.PtKoWsLGD
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



/-- `clear_account_preserving_balance` keeps the accounts-written table ready. -/
theorem clearAcct_rv_aqgdL (O0 : BitVec 64 → Prop) (Taw A0 Hl : BitVec 64) (la : TLay)
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
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
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
        (by omega) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe (koWs_fixed hkoWs reg1) ECH hECH)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ M' G' post => awPost_mono post h01))))
    (fun L M G ⟨ha,H,hH,hle,reg,hn,fr⟩ => by
      rcases hn with hn | ⟨_,hn⟩
      · exact ⟨(H,Nj,M),⟨ha,reg,rfl,hH,hn⟩,hle,fr,reg⟩
      · exact ⟨(H,Nj + 1,M),⟨ha,reg,rfl,hH,hn⟩,hle,fr,reg⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms clearAcct_rv_aqgdL
end cl2
end InitECandidate.Runtime
