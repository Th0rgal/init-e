import InitECandidate.Runtime.EncodeTxFrameGD
import InitECandidate.Runtime.ProcessTxUGD
/-!
`processTx_to_teNew_final` with the `encode_transaction` frame contract discharged by `encodeTx_frameCU` from an
explicit domain fence (`Fence D DF`, `DF + 8 ≤ 2^62`, heap cap `≤ DF`), carried as caller premises. Remaining
callee premise: the `recover_sender_with_chain_id` frame contract.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section pf
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs U : BitVec 64} {M0 : Mem}

/-- The actual `process_transaction` body from `bal_index = index + 1` to `te_new()`, with the `encode_transaction`,
`check_transaction` and `calculate_blob_gas_price` frame contracts discharged; the domain fence is an explicit
premise. Remaining callee premise: the `FrameCU` contract of `recover_sender_with_chain_id`. -/
theorem processTx_to_teNew_fenced {QM : Mem → GA → Prop} (Ix Arr : BitVec 64)
    -- explicit domain fence for encode_transaction (to be derived from the challenge arena at instantiation)
    {DF : Nat} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (fcRec : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id))
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
    -- get_code inside check_transaction
    (ne40 : k40 ≠ ko) (hc40 : c k40 = Ts + 40#64)
    -- the u256_ws workspace written by calculate_blob_gas_price
    (hU : U.toNat + 640 ≤ 2 ^ 64) (hwWS : ¬ WS U w) (hWO : ∀ x, WS U x → Out x ∧ ∀ i, x ≠ c i)
    (hWE : ∀ x, WS U x → Excl x)
    (hrest : AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 34 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction))  :=
  processTx_to_teNew_final Ix Arr (encodeTx_frameCU hF hDF hcap hwP) fcRec hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8
    hE8 hw8 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0
    hNB0 safe hOutSafe hkoWs hJE hSE ne40 hc40 hU hwWS hWO hWE hrest

#print axioms processTx_to_teNew_fenced
end pf
end InitECandidate.Runtime
