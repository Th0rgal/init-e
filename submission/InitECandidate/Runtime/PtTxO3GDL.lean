import InitECandidate.Runtime.PtTxO3GD
import InitECandidate.Runtime.PtKoWsLGD
import InitECandidate.Runtime.PtSegAllGDL
import InitECandidate.Runtime.PtSufAO2GDL
import InitECandidate.Runtime.PtSufBO2GDL
import InitECandidate.Runtime.PtRest2GDL
/-!
The actual `process_transaction` body with the interpreter contract `PmcCXB` (OPEN: `bal_*` globals and an exit snapshot
`SNAP`) and `incorporate_tx_into_block()` as `IncorpCO2`: after `out = process_message_call(m)` the suffix runs over the
arena with the `bal_*` globals pinned at their exit words (`JWB`, kept by every suffix callee through `BalKeep2`), and
the incorporate block validity `BV` is derived at the call from the exit snapshot, the suffix state, both block lists
and the pinned `bal_*` globals (`hBVc`, a derivation obligation, not a staging premise).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section c98c
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}
  {SNAP : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Mem → Prop}

/-- The actual `process_transaction` body from the `out = process_message_call(m)` site (spine drop 98) to its
`return 0` under `PmcCX`; `incorporate_tx_into_block()` is the named staging contract `IncorpCO2` at the reachable
suffix state (record words outside the registry, PMC-exit memory as base, raised arena bound). -/
theorem processTx_pmcX_to_end3L {QM : Mem → GA → Prop} (bk : BalKeep2) (Ix Rarr L40 L72 : BitVec 64)
    (pcx : PmcCXB SP0 P0 FM G0 J C SKB Bo U Sc w n c T Out ko D B Excl SNAP
      (sourceFunctionBody Guest.guestFn_process_message_call))
    (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
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
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x)
    (hBoC : ∀ k : BitVec 64, k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64 →
      (Out (Bo + k) ∧ ∀ i, Bo + k ≠ c i) ∧ Excl (Bo + k) ∧ w ≠ Bo + k)
    (hR32D : D (Bo + 32)) (hR32O : Out (Bo + 32)) (hR32E : ¬ Excl (Bo + 32)) (hRarr : M0 (Bo + 32) = .word Rarr)
    (hRO0 : Out (Rarr + Ix * 16) ∧ ∀ i, Rarr + Ix * 16 ≠ c i) (hRE0 : Excl (Rarr + Ix * 16))
    (hRw0 : w ≠ Rarr + Ix * 16)
    (hRO8 : Out (Rarr + Ix * 16 + 8) ∧ ∀ i, Rarr + Ix * 16 + 8 ≠ c i) (hRE8 : Excl (Rarr + Ix * 16 + 8))
    (hRw8 : w ≠ Rarr + Ix * 16 + 8)
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hExclP0 : ∀ x, Excl' x → x.toNat < P0.toNat) (hsub : ∀ x, Excl x → Excl' x)
    (hW40 : ∀ x, W40 x → BW n c Out Excl' w x) (hW72 : ∀ x, W72 x → BW n c Out Excl' w x)
    (hdis : ∀ x, W40 x → ¬ W72 x)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl' (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl' (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hL40 : BL0 W40 Excl Out P0 L40 M0) (hL72 : BL0 W72 Excl Out P0 L72 M0)
    (hWJ40 : ∀ x, W40 x → ¬ InJ J C x ∧ ¬ SkWin SKB x) (hWJ72 : ∀ x, W72 x → ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (ECH : BitVec 64) (hECH : G0.lookup (ofString "empty_code_hash") = some (.val (.word ECH)))
    (Wbal : BitVec 64 → Prop) (BV BVo : BitVec 64 → Mem → GA → Prop)
    (hWb : ∀ x, Wbal x → Out x ∧ ¬ Excl' x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hBVou : ∀ (Y : BitVec 64) M G (gname : MlS) (y : BitVec 64), (gname = ofString "scratch_ptr" ∨ gname = ofString "frame_mem_ptr") →
      BVo Y M G → BVo Y M (G.update (gname,.val (.word y))))
    (hBVc : ∀ (Y Hp : BitVec 64) (Mp : Mem) (BA IA IS KB Ixb : BitVec 64), SNAP BA IA IS KB Ixb Y Hp Mp →
      ∀ (Hb Hg : BitVec 64) (L : GA) (M : Mem) (G : GA), (LPSo Y Ix L ∧
        PZ n c T (fun x => Out x ∨ ORec Y x) ko D B (fun x => Excl' x ∨ Wbal x) Hb Hg Mp M G) ∧
        BL2 W40 W72 Hb L40 L72 M G → BalG BA IA IS KB Ixb G → BV Y M G)
    (hinc : ∀ (Y Hp : BitVec 64) (Mp : Mem) (Hb : BitVec 64), w.toNat < Hp.toNat → IncorpCO2 D B w RR SP0 Hp FM G0 J C SKB Bo U Sc n c T
      (fun x => Out x ∨ ORec Y x) ko (fun x => Excl' x ∨ Wbal x) W40 W72 (BV Y) (BVo Y) Mp Y Ix Hb L40 L72)
    (hRet : ∀ (Y : BitVec 64) (Mp : Mem) (Hb Hg : BitVec 64) L M G,
      (LPSo Y Ix L ∧ PZ n c T (fun x => Out x ∨ ORec Y x) ko D B (fun x => Excl' x ∨ Wbal x) Hb Hg Mp M G) ∧
        BL2 W40 W72 Hb L40 L72 M G ∧ BVo Y M G → RR (.val (.word 0#64)) M G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 98 (sourceFunctionBody Guest.guestFn_process_transaction)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_process_transaction,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,stateInitSpineDrop]
  refine aqgd_decCall_pmcXB Ix _ p0 pcx (fun Y Hp Mp BA IA IS KB Ixb p1 p2 orc fr sn => aqgd_enterB ?_)
    (fun _ _ _ _ _ _ _ h => h)
  have hHp : Hp.toNat < 2 ^ 64 := Hp.isLt
  have hwP' : w.toNat < Hp.toNat := by omega
  have hOS : ∀ x, (Out x ∨ ORec Y x) → WsSafe SP0 FM K Pd NB x ∧ x.toNat < Hp.toNat := fun x hx => by
    rcases hx with ho | ⟨lo,hi⟩
    · exact ⟨(hOutSafe x ho).1,by have := (hOutSafe x ho).2; omega⟩
    · exact ⟨hWsP0 x (by omega),by omega⟩
  have e80 : (Y + 80#64).toNat = Y.toNat + 80 := by rw [BitVec.toNat_add]; simp; omega
  have e88 : (Y + 88#64).toNat = Y.toNat + 88 := by rw [BitVec.toNat_add]; simp; omega
  refine ptSufAO2L (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ixb := Ixb) bk (P0 := Hp) (Out := fun x => Out x ∨ ORec Y x) (M0 := Mp) (H0 := Hp) Ix ne ne16 hAB hAo hBo hTs hBs
    hcA hcB hco hcd hc16 (le_refl _) jfit hwJ hwP' (Or.inl hOut) hwS (fun x hx => Or.inl (hJO x hx))
    (fun x hx => ⟨Or.inl (hSO x hx).1,(hSO x hx).2⟩) jsep K Pd NB hK0 hPd0 hNB0 safe hOS hkoWs hJE hSE
    (fun k hk => let b := hBoC k hk; ⟨⟨Or.inl b.1.1,b.1.2⟩,b.2⟩) ?_
  refine ptSufBO2L bk (P0 := Hp) (Out := fun x => Out x ∨ ORec Y x) (M0 := Mp) (H0 := Hp) Ix Rarr hF hDF hcap K Pd NB
    hK0 hPd0 safe hOS hkoWs (Or.inl hOut) hR32D (Or.inl hR32O) hR32E ((fr _ hR32O hR32E).trans hRarr)
    ⟨Or.inl hRO0.1,hRO0.2⟩ hRE0 hRw0 ⟨Or.inl hRO8.1,hRO8.2⟩ hRE8 hRw8 ?_
  exact ptSufD_126O2 bk (P0 := Hp) (Out := fun x => Out x ∨ ORec Y x) (M0 := Mp) (H0 := Hp) Ix L40 L72 hsub
    (fun x hx => let b := hW40 x hx; ⟨Or.inl b.1,b.2⟩) (fun x hx => let b := hW72 x hx; ⟨Or.inl b.1,b.2⟩) hdis
    (Or.inl hOut) ⟨Or.inl hB40.1,hB40.2.1,(fr _ hB40.1 (fun e => hB40.2.1 (hsub _ e))).trans hB40.2.2⟩
    ⟨Or.inl hB72.1,hB72.2.1,(fr _ hB72.1 (fun e => hB72.2.1 (hsub _ e))).trans hB72.2.2⟩
    (bl0_rebase hL40 (fun x h => Or.inl h) fr (by omega)) (bl0_rebase hL72 (fun x h => Or.inl h) fr (by omega))
    (fun Hb Nj Nl Lp h0 => ptRest134O3L bk Y Ix L40 L72 Hb Nj Nl Lp ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 jfit
      hwJ hwP' (Or.inl hOut) hwS (fun x hx => Or.inl (hJO x hx)) (fun x hx => ⟨Or.inl (hSO x hx).1,(hSO x hx).2⟩)
      jsep K Pd NB hK0 hPd0 hNB0 safe hOS hkoWs (fun x hx => hWsP0 x (by omega)) (fun x hx => hsub x (hJE x hx))
      (fun x hx => hsub x (hSE x hx)) h0 ECH hECH (fun x hx => ⟨Or.inl (hW40 x hx).1,hWJ40 x hx⟩)
      (fun x hx => ⟨Or.inl (hW72 x hx).1,hWJ72 x hx⟩) Wbal (BV Y) (BVo Y)
      (fun Hg L M G h bg => hBVc Y Hp Mp BA IA IS KB Ixb sn Hb Hg L M G h bg) (hBVou Y) (hinc Y Hp Mp Hb hwP') orc
      ⟨⟨Or.inr ⟨by omega,by omega⟩,fun h => by
          rcases h with h | h
          · have := hExclP0 _ h; omega
          · have := (hOutSafe _ (hWb _ h).1).2; omega⟩,
        ⟨Or.inr ⟨by omega,by omega⟩,fun h => by
          rcases h with h | h
          · have := hExclP0 _ h; omega
          · have := (hOutSafe _ (hWb _ h).1).2; omega⟩⟩ (hRet Y Mp Hb))

#print axioms processTx_pmcX_to_end3L
end c98c
section c1c
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 k40 : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}
  {SNAP : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Mem → Prop}

/-- The actual `process_transaction` body (spine drop 1 to `return 0`) with the interpreter output record threaded:
the named staging contracts are `PmcCX` (interpreter) and `IncorpCO2` (`incorporate_tx_into_block()` at the reachable
suffix state); the transaction-entry block lists and the return relation are explicit. -/
theorem processTx_fullO3L {QM : Mem → GA → Prop} (bk : BalKeep2) (Ix Arr Rarr L40 L72 : BitVec 64)
    (pcx : PmcCXB SP0 P0 FM G0 J C SKB Bo U Sc w n c T Out ko D B Excl SNAP
      (sourceFunctionBody Guest.guestFn_process_message_call))
    {DF : Nat} (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (hSc0 : Sc ≠ 0)
    (hwSc : ¬ MWin Sc 448 w) (hScE : ∀ x, MWin Sc 448 x → Excl x)
    (scSafe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → ¬ MWin Sc 448 x)
    (hkoSc : TabAvoid (fun x => ¬ MWin Sc 448 x) (T ko))
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
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
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
    (hExclP0 : ∀ x, Excl' x → x.toNat < P0.toNat) (hsub : ∀ x, Excl x → Excl' x)
    (hW40 : ∀ x, W40 x → BW n c Out Excl' w x) (hW72 : ∀ x, W72 x → BW n c Out Excl' w x)
    (hdis : ∀ x, W40 x → ¬ W72 x)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl' (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl' (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hL40 : BL0 W40 Excl Out P0 L40 M0) (hL72 : BL0 W72 Excl Out P0 L72 M0)
    (hWJ40 : ∀ x, W40 x → ¬ InJ J C x ∧ ¬ SkWin SKB x) (hWJ72 : ∀ x, W72 x → ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (ECH : BitVec 64) (hECH : G0.lookup (ofString "empty_code_hash") = some (.val (.word ECH)))
    (Wbal : BitVec 64 → Prop) (BV BVo : BitVec 64 → Mem → GA → Prop)
    (hWb : ∀ x, Wbal x → Out x ∧ ¬ Excl' x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hBVou : ∀ (Y : BitVec 64) M G (gname : MlS) (y : BitVec 64), (gname = ofString "scratch_ptr" ∨ gname = ofString "frame_mem_ptr") →
      BVo Y M G → BVo Y M (G.update (gname,.val (.word y))))
    (hBVc : ∀ (Y Hp : BitVec 64) (Mp : Mem) (BA IA IS KB Ixb : BitVec 64), SNAP BA IA IS KB Ixb Y Hp Mp →
      ∀ (Hb Hg : BitVec 64) (L : GA) (M : Mem) (G : GA), (LPSo Y Ix L ∧
        PZ n c T (fun x => Out x ∨ ORec Y x) ko D B (fun x => Excl' x ∨ Wbal x) Hb Hg Mp M G) ∧
        BL2 W40 W72 Hb L40 L72 M G → BalG BA IA IS KB Ixb G → BV Y M G)
    (hinc : ∀ (Y Hp : BitVec 64) (Mp : Mem) (Hb : BitVec 64), w.toNat < Hp.toNat → IncorpCO2 D B w RR SP0 Hp FM G0 J C SKB Bo U Sc n c T
      (fun x => Out x ∨ ORec Y x) ko (fun x => Excl' x ∨ Wbal x) W40 W72 (BV Y) (BVo Y) Mp Y Ix Hb L40 L72)
    (hRet : ∀ (Y : BitVec 64) (Mp : Mem) (Hb Hg : BitVec 64) L M G,
      (LPSo Y Ix L ∧ PZ n c T (fun x => Out x ∨ ORec Y x) ko D B (fun x => Excl' x ∨ Wbal x) Hb Hg Mp M G) ∧
        BL2 W40 W72 Hb L40 L72 M G ∧ BVo Y M G → RR (.val (.word 0#64)) M G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction)) :=
  processTx_to_pmcSL Ix Arr hF (by omega) hcap hSc0 hwSc hScE scSafe hkoSc hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8 hE8
    hw8 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0
    safe hOutSafe hkoWs hJE hSE ne40 hc40 hU hwWS hWO hWE hWsP0
    (processTx_pmcX_to_end3L bk Ix Rarr L40 L72 pcx hF hDF hcap ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit
      hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE hBoC hR32D hR32O hR32E hRarr
      hRO0 hRE0 hRw0 hRO8 hRE8 hRw8 hWsP0 hExclP0 hsub hW40 hW72 hdis hB40 hB72 hL40 hL72 hWJ40 hWJ72 ECH hECH Wbal BV
      BVo hWb hBVou hBVc hinc hRet)

#print axioms processTx_fullO3L
end c1c
end InitECandidate.Runtime
