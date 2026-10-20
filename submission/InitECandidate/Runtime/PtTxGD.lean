import InitECandidate.Runtime.PtRestAllGD
/-!
The actual `process_transaction` body from spine drop 1 to its `return 0`: every callee discharged except the named
staging contracts `PmcC` (interpreter entry `process_message_call`), `IncorpC` (`incorporate_tx_into_block()` at the
suffix call site) and the interpreter-output obligation `OutRecObl` (frame release marks); the transaction-entry
block-list validity (`BL0`) and the return relation are explicit.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section c1
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 k40 : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- The actual `process_transaction` body (spine drop 1 to `return 0`). -/
theorem processTx_fullS {QM : Mem → GA → Prop} (Ix Arr Rarr L40 L72 : BitVec 64)
    (pc : PmcC SP0 P0 FM G0 J C SKB Bo U Sc w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_process_message_call))
    {DF : Nat} (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (hSc0 : Sc ≠ 0)
    (hwSc : ¬ MWin Sc 448 w) (hScE : ∀ x, MWin Sc 448 x → Excl x)
    (scSafe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → ¬ MWin Sc 448 x)
    (hkoSc : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → ¬ MWin Sc 448 x)
    (hBoD : D (Bo + 24)) (hBoO : Out (Bo + 24)) (hBoE : ¬ Excl (Bo + 24)) (hArr : M0 (Bo + 24) = .word Arr)
    (hO0 : Out (Arr + Ix * 16) ∧ ∀ i, Arr + Ix * 16 ≠ c i) (hE0 : Excl (Arr + Ix * 16)) (hw0 : w ≠ Arr + Ix * 16)
    (hO8 : Out (Arr + Ix * 16 + 8) ∧ ∀ i, Arr + Ix * 16 + 8 ≠ c i) (hE8 : Excl (Arr + Ix * 16 + 8))
    (hw8 : w ≠ Arr + Ix * 16 + 8)
    (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
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
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x)
    (ne40 : k40 ≠ ko) (hc40 : c k40 = Ts + 40#64)
    (hU : U.toNat + 640 ≤ 2 ^ 64) (hwWS : ¬ WS U w) (hWO : ∀ x, WS U x → Out x ∧ ∀ i, x ≠ c i)
    (hWE : ∀ x, WS U x → Excl x)
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hBoC : ∀ k : BitVec 64, k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64 →
      (Out (Bo + k) ∧ ∀ i, Bo + k ≠ c i) ∧ Excl (Bo + k) ∧ w ≠ Bo + k)
    (hR32D : D (Bo + 32)) (hR32O : Out (Bo + 32)) (hR32E : ¬ Excl (Bo + 32)) (hRarr : M0 (Bo + 32) = .word Rarr)
    (hRO0 : Out (Rarr + Ix * 16) ∧ ∀ i, Rarr + Ix * 16 ≠ c i) (hRE0 : Excl (Rarr + Ix * 16))
    (hRw0 : w ≠ Rarr + Ix * 16)
    (hRO8 : Out (Rarr + Ix * 16 + 8) ∧ ∀ i, Rarr + Ix * 16 + 8 ≠ c i) (hRE8 : Excl (Rarr + Ix * 16 + 8))
    (hRw8 : w ≠ Rarr + Ix * 16 + 8)
    (hsub : ∀ x, Excl x → Excl' x)
    (hW40 : ∀ x, W40 x → BW n c Out Excl' w x) (hW72 : ∀ x, W72 x → BW n c Out Excl' w x)
    (hdis : ∀ x, W40 x → ¬ W72 x)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl' (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl' (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hL40 : BL0 W40 Excl Out P0 L40 M0) (hL72 : BL0 W72 Excl Out P0 L72 M0)
    (hWJ40 : ∀ x, W40 x → ¬ InJ J C x ∧ ¬ SkWin SKB x) (hWJ72 : ∀ x, W72 x → ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (ECH : BitVec 64) (hECH : G0.lookup (ofString "empty_code_hash") = some (.val (.word ECH)))
    (hinc : ∀ Hb : BitVec 64, IncorpC D B w RR SP0 P0 FM G0 J C SKB Bo U Sc n c T Out ko Excl' W40 W72 M0 Ix Hb L40 L72)
    (hOR : ∀ Hb : BitVec 64, OutRecObl D B SP0 FM n c T Out ko Excl' W40 W72 M0 Ix Hb L40 L72)
    (hRet : ∀ (Hb Hg : BitVec 64) L M G, (LPS Ix L ∧ PZ n c T Out ko D B Excl' Hb Hg M0 M G) ∧
      BL2 W40 W72 Hb L40 L72 M G → RR (.val (.word 0#64)) M G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction)) :=
  processTx_to_delS Ix Arr Rarr L40 L72 pc hF hDF hcap hSc0 hwSc hScE scSafe hkoSc hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8
    hE8 hw8 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0
    hNB0 safe hOutSafe hkoWs hJE hSE ne40 hc40 hU hwWS hWO hWE hWsP0 hBoC hR32D hR32O hR32E hRarr hRO0 hRE0 hRw0
    hRO8 hRE8 hRw8 hsub hW40 hW72 hdis hB40 hB72 hL40 hL72
    (fun Hb Nj Nl Lp h0 => ptRest134_aqgd Ix L40 L72 Hb Nj Nl Lp ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16
      jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hWsP0
      (fun x hx => hsub x (hJE x hx)) (fun x hx => hsub x (hSE x hx)) (by omega) ECH hECH
      (fun x hx => ⟨(hW40 x hx).1,hWJ40 x hx⟩) (fun x hx => ⟨(hW72 x hx).1,hWJ72 x hx⟩) (hinc Hb) (hOR Hb)
      (hRet Hb))

#print axioms processTx_fullS
end c1
end InitECandidate.Runtime
