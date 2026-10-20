import InitECandidate.Runtime.PtTxOGD
import InitECandidate.Runtime.PtIncorpCO2GD
/-!
The actual `process_transaction` body with `incorporate_tx_into_block()` as `IncorpCO2` (block validity over memory and
globals). Compatible with `processTx_fullO`: the suffix, deletion frames and return relation are unchanged; the block
validity `BV` is stated at the reachable state at `del` (explicit, to be earned by the reachable interpreter), kept by the
deletion frames, and `BVo` by the tail's pointer updates.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ra2
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- The actual remainder `ptRest134` of `process_transaction` from the suffix state at `del`, with block validity over
memory and globals and `incorporate_tx_into_block()` as `IncorpCO2`: `BV` holds at the reachable state at `del`, is kept
by the deletion frames (heap pointer only growing, the block-access-list words kept), and `BVo` by the scratch and
frame pointer updates of the tail. -/
theorem ptRest134O2 {QM : Mem → GA → Prop} (Y Ix L40 L72 Hb Nj Nl Lp : BitVec 64)
    (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
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
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x) (hP0Hb : P0.toNat ≤ Hb.toNat)
    (ECH : BitVec 64) (hECH : G0.lookup (ofString "empty_code_hash") = some (.val (.word ECH)))
    (hW40 : ∀ x, W40 x → Out x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hW72 : ∀ x, W72 x → Out x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (Wbal : BitVec 64 → Prop) (BV BVo : Mem → GA → Prop)
    (hWb : ∀ x, Wbal x → Out x ∧ ¬ Excl x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hBVf : ∀ (M M' : Mem) (G G' : GA) (H H' : BitVec 64), BV M G → HeapIs G H → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x, Wbal x → M' x = M x) → BV M' G')
    (hBVou : ∀ M G (gname : MlS) (y : BitVec 64), (gname = ofString "scratch_ptr" ∨ gname = ofString "frame_mem_ptr") →
      BVo M G → BVo M (G.update (gname,.val (.word y))))
    (hBV0 : ∀ M G, PB n c T Out ko D B Excl Hb Nj M0 M G → BV M G)
    (hinc : IncorpCO2 D B w RR SP0 P0 FM G0 J C SKB Bo U Sc n c T Out ko (fun x => Excl x ∨ Wbal x) W40 W72 BV BVo M0 Y
      Ix Hb L40 L72)
    (hORm : OutRec SP0 FM Y M0)
    (hYO : (Out (Y + 80#64) ∧ ¬ (Excl (Y + 80#64) ∨ Wbal (Y + 80#64))) ∧
      (Out (Y + 88#64) ∧ ¬ (Excl (Y + 88#64) ∨ Wbal (Y + 88#64))))
    (hRet : ∀ (Hg : BitVec 64) L M G, (LPSo Y Ix L ∧ PZ n c T Out ko D B (fun x => Excl x ∨ Wbal x) Hb Hg M0 M G) ∧
      BL2 W40 W72 Hb L40 L72 M G ∧ BVo M G → RR (.val (.word 0#64)) M G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR ptRest134 := by
  unfold ptRest134
  refine aqgd_conseqA (P' := fun L M G => ∃ Hg : BitVec 64, (LPSo Y Ix L ∧
      PZ n c T Out ko D B (fun x => Excl x ∨ Wbal x) Hb Hg M0 M G) ∧ BL2 W40 W72 Hb L40 L72 M G ∧ BV M G)
    (aqgd_exE (fun Hg => ?_)) ?_
  · refine ptRest_delO (R := fun M G => BL2 W40 W72 Hb L40 L72 M G ∧ BV M G) Ix ne ne16 hAB hAo hBo hTs hBs hcA hcB hco
      hcd hc16 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hWsP0
      (fun x hx => Or.inl (hJE x hx)) (fun x hx => Or.inl (hSE x hx)) hP0Hb ECH hECH
      (fun M M' G G' H H' ⟨bls,bv⟩ hH hH' le keep => ⟨⟨bl_frameX bls.1 hW40 hH hH' le keep,
        bl_frameX bls.2 hW72 hH hH' le keep⟩,hBVf M M' G G' H H' bv hH hH' le (fun x hx => let k := hWb x hx;
          keep x (Or.inl k.1) k.2.2.1 k.2.2.2)⟩) ?_
    refine aqgd_seq (hinc Hg) (aqgd_conseq (P := fun L M G =>
        ((LPSo Y Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))) ∧
          PZ n c T Out ko D B (fun x => Excl x ∨ Wbal x) Hb Hg M0 M G) ∧
          (BL2 W40 W72 Hb L40 L72 M G ∧ BVo M G) ∧ OutRec SP0 FM Y M)
      (ptRest_tailO Ix Y
        (fun M G gname y hg ⟨bls,bv⟩ => by
          have hn : ofString "heap_ptr" ≠ gname := by rcases hg with rfl | rfl <;> decide
          exact ⟨⟨bl_gupd bls.1 _ _ hn,bl_gupd bls.2 _ _ hn⟩,hBVou M G _ _ hg bv⟩)
        (fun L M G ⟨⟨lp,pz⟩,bls,bv⟩ => hRet Hg L M G ⟨⟨lp,pz⟩,bls,bv⟩)) ?_ (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    intro L M G ⟨⟨lp,pz⟩,bls,bv⟩
    have fr : ∀ x, Out x → ¬ (Excl x ∨ Wbal x) → M x = M0 x := by obtain ⟨_,_,_,_,_,_,fr⟩ := pz; exact fr
    have k80 := fr _ hYO.1.1 hYO.1.2
    have k88 := fr _ hYO.2.1 hYO.2.2
    refine ⟨⟨⟨lp,lp.2⟩,pz⟩,⟨bls,bv⟩,?_⟩
    unfold OutRec at hORm ⊢
    rw [k80,k88]; exact hORm
  · intro L M G _ ⟨⟨ld,pb⟩,b40,b72⟩
    obtain ⟨H,hH,_⟩ := pb.1
    exact ⟨H,⟨ld.1,pz_excl (pz_of_pb hAB pb hH) (fun x h => Or.inl h)⟩,⟨b40,b72⟩,
      hBV0 M G pb⟩

#print axioms ptRest134O2
end ra2
section c98b
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- The actual `process_transaction` body from the `out = process_message_call(m)` site (spine drop 98) to its
`return 0` under `PmcCX`; `incorporate_tx_into_block()` is the named staging contract `IncorpCO2` at the reachable
suffix state (record words outside the registry, PMC-exit memory as base, raised arena bound). -/
theorem processTx_pmcX_to_end2 {QM : Mem → GA → Prop} (Ix Rarr L40 L72 : BitVec 64)
    (pcx : PmcCX SP0 P0 FM G0 J C SKB Bo U Sc w n c T Out ko D B Excl
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
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
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
    (hBVf : ∀ (Y : BitVec 64) (M M' : Mem) (G G' : GA) (H H' : BitVec 64), BV Y M G → HeapIs G H → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x, Wbal x → M' x = M x) → BV Y M' G')
    (hBVou : ∀ (Y : BitVec 64) M G (gname : MlS) (y : BitVec 64), (gname = ofString "scratch_ptr" ∨ gname = ofString "frame_mem_ptr") →
      BVo Y M G → BVo Y M (G.update (gname,.val (.word y))))
    (hBVp : ∀ (Y : BitVec 64) (Mp : Mem) (Hb Nj : BitVec 64) M G,
      PB n c T (fun x => Out x ∨ ORec Y x) ko D B Excl' Hb Nj Mp M G → BV Y M G)
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
  refine aqgd_decCall_pmcX Ix _ p0 pcx (fun Y Hp Mp p1 p2 orc fr => ?_) (fun _ _ _ _ _ _ _ h => h)
  have hHp : Hp.toNat < 2 ^ 64 := Hp.isLt
  have hwP' : w.toNat < Hp.toNat := by omega
  have hOS : ∀ x, (Out x ∨ ORec Y x) → WsSafe SP0 FM K Pd NB x ∧ x.toNat < Hp.toNat := fun x hx => by
    rcases hx with ho | ⟨lo,hi⟩
    · exact ⟨(hOutSafe x ho).1,by have := (hOutSafe x ho).2; omega⟩
    · exact ⟨hWsP0 x (by omega),by omega⟩
  have e80 : (Y + 80#64).toNat = Y.toNat + 80 := by rw [BitVec.toNat_add]; simp; omega
  have e88 : (Y + 88#64).toNat = Y.toNat + 88 := by rw [BitVec.toNat_add]; simp; omega
  refine ptSufAO (P0 := Hp) (Out := fun x => Out x ∨ ORec Y x) (M0 := Mp) (H0 := Hp) Ix ne ne16 hAB hAo hBo hTs hBs
    hcA hcB hco hcd hc16 (le_refl _) jfit hwJ hwP' (Or.inl hOut) hwS (fun x hx => Or.inl (hJO x hx))
    (fun x hx => ⟨Or.inl (hSO x hx).1,(hSO x hx).2⟩) jsep K Pd NB hK0 hPd0 hNB0 safe hOS hkoWs hJE hSE
    (fun k hk => let b := hBoC k hk; ⟨⟨Or.inl b.1.1,b.1.2⟩,b.2⟩) ?_
  refine ptSufBO (P0 := Hp) (Out := fun x => Out x ∨ ORec Y x) (M0 := Mp) (H0 := Hp) Ix Rarr hF hDF hcap K Pd NB
    hK0 hPd0 safe hOS hkoWs (Or.inl hOut) hR32D (Or.inl hR32O) hR32E ((fr _ hR32O hR32E).trans hRarr)
    ⟨Or.inl hRO0.1,hRO0.2⟩ hRE0 hRw0 ⟨Or.inl hRO8.1,hRO8.2⟩ hRE8 hRw8 ?_
  exact ptSufD_126O (P0 := Hp) (Out := fun x => Out x ∨ ORec Y x) (M0 := Mp) (H0 := Hp) Ix L40 L72 hsub
    (fun x hx => let b := hW40 x hx; ⟨Or.inl b.1,b.2⟩) (fun x hx => let b := hW72 x hx; ⟨Or.inl b.1,b.2⟩) hdis
    (Or.inl hOut) ⟨Or.inl hB40.1,hB40.2.1,(fr _ hB40.1 (fun e => hB40.2.1 (hsub _ e))).trans hB40.2.2⟩
    ⟨Or.inl hB72.1,hB72.2.1,(fr _ hB72.1 (fun e => hB72.2.1 (hsub _ e))).trans hB72.2.2⟩
    (bl0_rebase hL40 (fun x h => Or.inl h) fr (by omega)) (bl0_rebase hL72 (fun x h => Or.inl h) fr (by omega))
    (fun Hb Nj Nl Lp h0 => ptRest134O2 Y Ix L40 L72 Hb Nj Nl Lp ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 jfit
      hwJ hwP' (Or.inl hOut) hwS (fun x hx => Or.inl (hJO x hx)) (fun x hx => ⟨Or.inl (hSO x hx).1,(hSO x hx).2⟩)
      jsep K Pd NB hK0 hPd0 hNB0 safe hOS hkoWs (fun x hx => hWsP0 x (by omega)) (fun x hx => hsub x (hJE x hx))
      (fun x hx => hsub x (hSE x hx)) h0 ECH hECH (fun x hx => ⟨Or.inl (hW40 x hx).1,hWJ40 x hx⟩)
      (fun x hx => ⟨Or.inl (hW72 x hx).1,hWJ72 x hx⟩) Wbal (BV Y) (BVo Y)
      (fun x hx => let k := hWb x hx; ⟨Or.inl k.1,k.2⟩) (hBVf Y) (hBVou Y) (hBVp Y Mp Hb Nj) (hinc Y Hp Mp Hb hwP') orc
      ⟨⟨Or.inr ⟨by omega,by omega⟩,fun h => by
          rcases h with h | h
          · have := hExclP0 _ h; omega
          · have := (hOutSafe _ (hWb _ h).1).2; omega⟩,
        ⟨Or.inr ⟨by omega,by omega⟩,fun h => by
          rcases h with h | h
          · have := hExclP0 _ h; omega
          · have := (hOutSafe _ (hWb _ h).1).2; omega⟩⟩ (hRet Y Mp Hb))

#print axioms processTx_pmcX_to_end2
end c98b
section c1b
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 k40 : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- The actual `process_transaction` body (spine drop 1 to `return 0`) with the interpreter output record threaded:
the named staging contracts are `PmcCX` (interpreter) and `IncorpCO2` (`incorporate_tx_into_block()` at the reachable
suffix state); the transaction-entry block lists and the return relation are explicit. -/
theorem processTx_fullO2 {QM : Mem → GA → Prop} (Ix Arr Rarr L40 L72 : BitVec 64)
    (pcx : PmcCX SP0 P0 FM G0 J C SKB Bo U Sc w n c T Out ko D B Excl
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
    (hBVf : ∀ (Y : BitVec 64) (M M' : Mem) (G G' : GA) (H H' : BitVec 64), BV Y M G → HeapIs G H → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x, Wbal x → M' x = M x) → BV Y M' G')
    (hBVou : ∀ (Y : BitVec 64) M G (gname : MlS) (y : BitVec 64), (gname = ofString "scratch_ptr" ∨ gname = ofString "frame_mem_ptr") →
      BVo Y M G → BVo Y M (G.update (gname,.val (.word y))))
    (hBVp : ∀ (Y : BitVec 64) (Mp : Mem) (Hb Nj : BitVec 64) M G,
      PB n c T (fun x => Out x ∨ ORec Y x) ko D B Excl' Hb Nj Mp M G → BV Y M G)
    (hinc : ∀ (Y Hp : BitVec 64) (Mp : Mem) (Hb : BitVec 64), w.toNat < Hp.toNat → IncorpCO2 D B w RR SP0 Hp FM G0 J C SKB Bo U Sc n c T
      (fun x => Out x ∨ ORec Y x) ko (fun x => Excl' x ∨ Wbal x) W40 W72 (BV Y) (BVo Y) Mp Y Ix Hb L40 L72)
    (hRet : ∀ (Y : BitVec 64) (Mp : Mem) (Hb Hg : BitVec 64) L M G,
      (LPSo Y Ix L ∧ PZ n c T (fun x => Out x ∨ ORec Y x) ko D B (fun x => Excl' x ∨ Wbal x) Hb Hg Mp M G) ∧
        BL2 W40 W72 Hb L40 L72 M G ∧ BVo Y M G → RR (.val (.word 0#64)) M G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction)) :=
  processTx_to_pmcS Ix Arr hF (by omega) hcap hSc0 hwSc hScE scSafe hkoSc hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8 hE8
    hw8 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0
    safe hOutSafe hkoWs hJE hSE ne40 hc40 hU hwWS hWO hWE hWsP0
    (processTx_pmcX_to_end2 Ix Rarr L40 L72 pcx hF hDF hcap ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit
      hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE hBoC hR32D hR32O hR32E hRarr
      hRO0 hRE0 hRw0 hRO8 hRE8 hRw8 hWsP0 hExclP0 hsub hW40 hW72 hdis hB40 hB72 hL40 hL72 hWJ40 hWJ72 ECH hECH Wbal BV
      BVo hWb hBVf hBVou hBVp hinc hRet)

#print axioms processTx_fullO2
end c1b
section hi
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB k40 : Fin n}
  {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop} {Sk : BitVec 64 → Prop}
  {Excl' Wbal W40 W72 Z : BitVec 64 → Prop} {Ix L40 L72 : BitVec 64}

/-- The staging premise of `processTx_fullO2` is met by the actual installed incorporate call with
`BV Y := IncW` (outside words `Out ∨ ORec Y`, excluded words `Excl' ∨ Wbal`) and `BVo Y := IncWo`. `BalKeep` and the
OPEN witness obligation `WsReadObl` (at every raised arena bound) stay explicit. -/
theorem hinc_of_incorpCO2_call (bk : BalKeep)
    (wsr : ∀ Hp : BitVec 64, w.toNat < Hp.toNat → WsReadObl D B (JWSBUS SP0 Hp FM G0 J C SKB Bo U Sc) WsI)
    (hAB : kA ≠ kB) (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) (ne40 : k40 ≠ ko) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c k40 = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    (Pw : BitVec 64) (hwZ : ¬ Z w) (hwPw : w.toNat < Pw.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    ∀ (Y Hp : BitVec 64) (Mp : Mem) (Hb : BitVec 64), w.toNat < Hp.toNat → IncorpCO2 D B w RR SP0 Hp FM G0 J C SKB
      Bo U Sc n c T (fun x => Out x ∨ ORec Y x) ko (fun x => Excl' x ∨ Wbal x) W40 W72
      (fun M G => IncW D B n c T WsI Sk Ts Bs Pw Z (fun x => Out x ∨ ORec Y x) (fun x => Excl' x ∨ Wbal x) W40 W72 M G)
      (fun M G => IncWo D B n c T ko WsI Sk M G) Mp Y Ix Hb L40 L72 :=
  fun _ Hp _ _ hwP => incorpCO2_call bk (wsr Hp hwP) hAB ne Bs hBs hcB ne40 Ts hTs hc40
    (fun x h => ⟨Or.inl (hSkSO x h).1,(hSkSO x h).2⟩) hSk Pw hwZ hwPw hwP Dall

#print axioms hinc_of_incorpCO2_call
end hi
end InitECandidate.Runtime
