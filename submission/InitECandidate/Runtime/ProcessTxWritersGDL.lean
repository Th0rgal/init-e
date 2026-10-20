import InitECandidate.Runtime.ProcessTxWritersGD
import InitECandidate.Runtime.PtKoWsLGD
/-!
The `process_transaction` sender-debit segment over the content-carrying registry: call rules for callees with
struct parameters (callee-entry scalar locals supplied by the caller), the actual `increment_nonce`,
`set_account_balance` and `u256_sub` calls keeping `PXR`, and the composition from `bal_index = index + 1` to the
`te_new()` declaration.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString




section gen
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}



end gen

section wr
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs : BitVec 64} {M0 : Mem}


/-- The actual `increment_nonce(sender)` call keeping `PXR` (journal and key-buffer writes inside `Excl`). -/
theorem aqgd_call_incNonceL {LP : GA → Prop} (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
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
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x)
    (hx : ∀ L, LP L → ∃ X : BitVec 64, L.lookup (ofString "sender") = some (.val (.word X))) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR
      (.call (some (none,none)) (ofString "increment_nonce") [.var .local (ofString "sender")]) := by
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1, HeapIs G0' H1 ∧ DAPost n c T Out ko D B J C SKB H1 M0' M' G')
    _ _ _ _ _ originalRuntimeCode_incrementNonce_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,h01,reg,hn,_⟩
    refine aqgd_conseq (aqgd_jwsb (incrementNonceT_aqgd (H0 := H1) (M0 := M0') (Nj := Nj) ne ne16 hAB hAo hBo hTs
      hBs hcA hcB hco hcd hc16 (le_trans p0 h01) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe
      hOutSafe (koWs_fixed hkoWs reg)) (keepsBo_of_installed originalRuntimeCode_incrementNonce_lookup (by decide)))
      ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨ha,reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro F s values callee rs _ H _ ⟨lp,_⟩ _ args lookup
    obtain ⟨X,hX⟩ := hx _ lp
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hX] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_incrementNonce_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨X,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,h01,_,_,fr⟩ ⟨H1',hH',post⟩
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨lp,pxr_of_dapost hJE hSE h01 fr post⟩

/-- The actual `set_account_balance(sender, bal)` call keeping `PXR`. -/
theorem aqgd_call_setBalL {LP : GA → Prop} (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
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
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR
      (.call (some (none,none)) (ofString "set_account_balance")
        [.var .local (ofString "sender"),.var .local (ofString "bal")]) := by
  refine aqgd_callSpecS (Vn' := fun x => x ≠ ofString "amount")
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1, HeapIs G0' H1 ∧ DAPost n c T Out ko D B J C SKB H1 M0' M' G')
    _ _ _ _ _ originalRuntimeCode_setAccountBalance_lookup (fun _ _ _ h => (setBal_callee h).1) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,h01,reg,hn,_⟩
    refine aqgd_conseq (aqgd_jwsb (setAccountBalanceT_aqgd (H0 := H1) (M0 := M0') (Nj := Nj) ne ne16 hAB hAo hBo hTs
      hBs hcA hcB hco hcd hc16 (le_trans p0 h01) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe
      hOutSafe (koWs_fixed hkoWs reg)) (keepsBo_of_installed originalRuntimeCode_setAccountBalance_lookup (by decide)))
      ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨ha,reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro F s values callee rs _ H _ _ _ _ lookup
    exact ⟨⟨(setBal_callee lookup).2.2,(setBal_callee lookup).2.1⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,h01,_,_,fr⟩ ⟨H1',hH',post⟩
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨lp,pxr_of_dapost hJE hSE h01 fr post⟩

/-- `bal = u256_sub(bal, x)`: a result-assigning read-only call keeping `LPS`. -/
theorem aqgd_u256Sub_lpsL {Ix : BitVec 64} {X : Mem → GA → Prop} {A : GA → Prop} (args : List (ExpHOL 64)) :
    AQGD D B A w (fun _ => False) (fun L M G => LPS Ix L ∧ X M G) (fun L M G => LPS Ix L ∧ X M G) RR
      (.call (some (some (.local,ofString "bal"),none)) (ofString "u256_sub") args) :=
  aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    _ _ _ _ _ _ originalRuntimeCode_u256Sub_lookup (fun _ _ _ _ _ h => h.elim) (fun h => h)
    (fun _ M0' G0' _ => aqgd_of_mf (memoryFrame_of_good originalRuntimeCode_u256Sub_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_u256_sub) (by body_check Guest.guestFn_u256_sub) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun L M G v M' G' pre ⟨e1,e2⟩ => by rw [e1,e2]; exact ⟨lps_upd pre.1 _ v (by decide) (by decide),pre.2⟩)

#print axioms aqgd_call_incNonceL
#print axioms aqgd_call_setBalL
#print axioms aqgd_u256Sub_lpsL
end wr

section pw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs : BitVec 64} {M0 : Mem}



end pw
end InitECandidate.Runtime
