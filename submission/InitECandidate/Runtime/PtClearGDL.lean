import InitECandidate.Runtime.PtClearGD
import InitECandidate.Runtime.PtKoWsLGD
/-!
The actual `clear_account_preserving_balance(addr)` over the content-carrying registry `RegT`: `destroy_storage(addr)`
(`DSPost`), then `get_account`, a fresh copy, the stores `a + 0 = 0` and `a + 48 = empty_code_hash` into the copy, and
the original `modify_state_commit` (`DAPost`). The tail is the `increment_nonce` proof with the two stores.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString




section cl
variable {SP0 P0 FM w : BitVec 64} {G0 : GA}
variable {D : BitVec 64 → Prop} {B : Bool}
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Ts Bs SKB J C Nj H0 : BitVec 64} {M0 : Mem}



/-- The actual `clear_account_preserving_balance(addr)` over the content-carrying registry. -/
theorem clearAcctPBT_aqgdL (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
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
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
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
      (H0.toNat ≤ q.1.toNat ∧ (∀ x, Out x → ¬ InJ J C x → ¬ SkWin SKB x → q.2.2 x = M0 x) ∧
        RegT n c T Out q.1 q.2.2 D B ko)))
    (aqgd_ex (fun q => aqgd_purePre (fun ⟨h01,fr,reg1⟩ => aqgd_conseq
      (clearTailT_aqgd (H0 := q.1) (Nj := q.2.1) (M0 := q.2.2) ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16
        (by omega) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe (koWs_fixed hkoWs reg1) ECH hECH)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ M' G' ⟨H',hH',hle,reg',hn',fr'⟩ => ⟨H',hH',by omega,reg',hn',
        fun x hx hj hs => (fr' x hx hj hs).trans (fr x hx hj hs)⟩))))
    (fun L M G ⟨ha,H,hH,hle,reg,hn,fr⟩ => by
      rcases hn with hn | ⟨_,hn⟩
      · exact ⟨(H,Nj,M),⟨ha,reg,rfl,hH,hn⟩,hle,fr,reg⟩
      · exact ⟨(H,Nj + 1,M),⟨ha,reg,rfl,hH,hn⟩,hle,fr,reg⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms clearAcctPBT_aqgdL
end cl
end InitECandidate.Runtime
