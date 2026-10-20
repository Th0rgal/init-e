import InitECandidate.Runtime.PtRestAllOGD
import InitECandidate.Runtime.PtSufBOGD
/-!
The actual `process_transaction` body with the interpreter output record threaded through the suffix. `PmcCX` is the
named interpreter contract (conditional until the interpreter proves it): `PmcC` together with the returned output record
`out = Y` (`[Y, Y + 96)` below the exit heap pointer and outside every registry footprint) and its release marks
(`OutRec`). The suffix (spine drops 99 on) runs at the arena bound raised to the exit heap pointer, with the record words
as outside words and the exit memory as base, so the marks are still there at the frame release.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section lw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- A triple over the process arena with its bound raised to the entry heap pointer `Hc ≥ P0` holds over the arena. -/
theorem aqgd_jwsbus_lower {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} {Hc : BitVec 64} (le : P0.toNat ≤ Hc.toNat)
    (h : AQGD D B (JWSBUS SP0 Hc FM G0 J C SKB Bo U Sc) w Vn P Q RR p) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => P L M G ∧ HeapIs G Hc) Q RR p := by
  intro F s code dom aw sl H hH ⟨pre,hc⟩
  unfold GIs at hH; subst hH
  have awH : JWSBUS SP0 Hc FM G0 J C SKB Bo U Sc s.globals :=
    ⟨⟨⟨⟨⟨(aw_raise aw.1.1.1.1.1 hc).1,aw.1.1.1.1.2⟩,aw.1.1.1.2⟩,aw.1.1.2⟩,aw.1.2⟩,aw.2⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom awH sl _ rfl pre
  exact ⟨m,fun cont => let x := a cont; ⟨⟨⟨⟨⟨(aw_lower x.1.1.1.1.1 le).1,x.1.1.1.1.2⟩,x.1.1.1.2⟩,x.1.1.2⟩,x.1.2⟩,x.2⟩,
    n,r,c,b⟩

#print axioms aqgd_jwsbus_lower
end lw

/-- The interpreter output record `[Y, Y + 96)`. -/
def ORec (Y x : BitVec 64) : Prop := Y.toNat ≤ x.toNat ∧ x.toNat < Y.toNat + 96

/-- Named interpreter contract (conditional until the interpreter proves it): `PmcC` and the returned output record. -/
def PmcCX (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo U Sc : BitVec 64) (w : BitVec 64) (n : Nat)
    (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (body : ProgHOL 64) : Prop :=
  ∀ (H1 Nj : BitVec 64) (M0 : Mem),
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => True)
      (fun _ M G => RegT n c T Out H1 M D B ko ∧ M = M0 ∧ HeapIs G H1 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True)
      (fun v M' G' => ∃ Y H' : BitVec 64, v = .val (.word Y) ∧ HeapIs G' H' ∧ H1.toNat ≤ Y.toNat ∧
        Y.toNat + 96 ≤ H'.toNat ∧ RegT n c T (fun x => Out x ∨ ORec Y x) H' M' D B ko ∧
        (∃ Nj' : BitVec 64, G'.lookup (ofString "journal_n") = some (.val (.word Nj'))) ∧
        (∀ x, Out x → ¬ Excl x → M' x = M0 x) ∧ OutRec SP0 FM Y M')
      body

section pm
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc H0 : BitVec 64} {M0 : Mem}

/-- `out = process_message_call(e)` under `PmcCX`: the continuation runs at the arena bound raised to the exit heap
pointer `Hp`, with `out = Y`, the record words as outside words of the registry, and the exit memory `Mp` as base. -/
theorem aqgd_decCall_pmcX {Q Q2 : GA → Mem → GA → Prop} (Ix : BitVec 64) (e : ExpHOL 64) {cont : ProgHOL 64}
    (p0 : P0.toNat ≤ H0.toNat) (pc : PmcCX SP0 P0 FM G0 J C SKB Bo U Sc w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_process_message_call))
    (hcont : ∀ (Y Hp : BitVec 64) (Mp : Mem), P0.toNat ≤ Y.toNat → Y.toNat + 96 ≤ Hp.toNat →
      OutRec SP0 FM Y Mp → (∀ x, Out x → ¬ Excl x → Mp x = M0 x) →
      AQGD D B (JWSBUS SP0 Hp FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => LPSo Y Ix L ∧ PXR n c T (fun x => Out x ∨ ORec Y x) ko D B Excl Hp Mp M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (ofString "out",L.lookup (ofString "out"))) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q2 RR
      (.decCall (ofString "out") .one (ofString "process_message_call") [e] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1 : BitVec 64, HeapIs G0' H1 ∧ ∃ Y H' : BitVec 64, v = .val (.word Y) ∧ HeapIs G' H' ∧ H1.toNat ≤ Y.toNat ∧
        Y.toNat + 96 ≤ H'.toNat ∧ RegT n c T (fun x => Out x ∨ ORec Y x) H' M' D B ko ∧
        (∃ Nj' : BitVec 64, G'.lookup (ofString "journal_n") = some (.val (.word Nj'))) ∧
        (∀ x, Out x → ¬ Excl x → M' x = M0' x) ∧ OutRec SP0 FM Y M')
    (Pc := fun L M G => ∃ q : BitVec 64 × BitVec 64 × Mem, ((LPSo q.1 Ix L ∧
      PXR n c T (fun x => Out x ∨ ORec q.1 x) ko D B Excl q.2.1 q.2.2 M G) ∧ HeapIs G q.2.1) ∧
      (P0.toNat ≤ q.1.toNat ∧ q.1.toNat + 96 ≤ q.2.1.toNat ∧ OutRec SP0 FM q.1 q.2.2 ∧
        ∀ x, Out x → ¬ Excl x → q.2.2 x = M0 x))
    (Qc := Q) _ _ _ _ _ _ _ originalRuntimeCode_processMessageCall_lookup (by simp) ?_
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_
    (aqgd_ex (fun q => aqgd_purePre (fun ⟨p1,p2,orc,fr⟩ => aqgd_jwsbus_lower (by omega)
      (hcont q.1 q.2.1 q.2.2 p1 p2 orc fr)))) hres
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,_,reg,hn,_⟩
    refine aqgd_conseq (pc H1 Nj M0') ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hM,hG⟩
      subst hM hG
      exact ⟨reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,hle,_,_,fr⟩ ⟨H1',hH',Y,H',ev,hH2,hY,hYH,reg',⟨Nj',hn'⟩,fr',orc⟩ _
    have e := heapIs_unique hH hH'
    subst e ev
    have p1 : P0.toNat ≤ Y.toNat := by omega
    exact ⟨(Y,H',M'),⟨⟨⟨lps_upd lp _ _ (by decide) (by decide),lookup_update_eq' _ _ _⟩,
      H',Nj',hH2,le_refl _,reg',hn',fun _ _ _ => rfl⟩,hH2⟩,p1,hYH,orc,
      fun x ho hx => (fr' x ho hx).trans (fr x ho hx)⟩

#print axioms aqgd_decCall_pmcX
end pm
theorem bl0_rebase {Wb Excl Out Out' : BitVec 64 → Prop} {P0 Hp Lh : BitVec 64} {M0 Mp : Mem}
    (h : BL0 Wb Excl Out P0 Lh M0) (sub : ∀ x, Out x → Out' x) (fr : ∀ x, Out x → ¬ Excl x → Mp x = M0 x)
    (le : P0.toNat ≤ Hp.toNat) : BL0 Wb Excl Out' Hp Lh Mp := by
  obtain ⟨hW,hL,P,N,Cp,⟨d0,d8,d16⟩,hNC,hC0,hbuf,inW⟩ := h
  have k : ∀ x, HdW Lh x → Mp x = M0 x := fun x hx => fr x (hW x hx).1 (hW x hx).2.1
  exact ⟨fun x hx => ⟨sub x (hW x hx).1,(hW x hx).2⟩,by omega,P,N,Cp,⟨(k _ (Or.inl rfl)).trans d0,
    (k _ (Or.inr (Or.inl rfl))).trans d8,(k _ (Or.inr (Or.inr rfl))).trans d16⟩,hNC,hC0,by omega,inW⟩

section c98
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- The actual `process_transaction` body from the `out = process_message_call(m)` site (spine drop 98) to its
`return 0` under `PmcCX`; `incorporate_tx_into_block()` is the named staging contract `IncorpCO` at the reachable
suffix state (record words outside the registry, PMC-exit memory as base, raised arena bound). -/
theorem processTx_pmcX_to_end {QM : Mem → GA → Prop} (Ix Rarr L40 L72 : BitVec 64)
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
    (Wbal : BitVec 64 → Prop) (BV BVo : Mem → Prop)
    (hWb : ∀ x, Wbal x → Out x ∧ ¬ Excl' x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hBVf : ∀ M M', BV M → (∀ x, Wbal x → M' x = M x) → BV M') (hBV0 : BV M0)
    (hinc : ∀ (Y Hp : BitVec 64) (Mp : Mem) (Hb : BitVec 64), IncorpCO D B w RR SP0 Hp FM G0 J C SKB Bo U Sc n c T
      (fun x => Out x ∨ ORec Y x) ko (fun x => Excl' x ∨ Wbal x) W40 W72 BV BVo Mp Y Ix Hb L40 L72)
    (hRet : ∀ (Y : BitVec 64) (Mp : Mem) (Hb Hg : BitVec 64) L M G,
      (LPSo Y Ix L ∧ PZ n c T (fun x => Out x ∨ ORec Y x) ko D B (fun x => Excl' x ∨ Wbal x) Hb Hg Mp M G) ∧
        BL2 W40 W72 Hb L40 L72 M G ∧ BVo M → RR (.val (.word 0#64)) M G) :
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
    (fun Hb Nj Nl Lp h0 => ptRest134O Y Ix L40 L72 Hb Nj Nl Lp ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 jfit
      hwJ hwP' (Or.inl hOut) hwS (fun x hx => Or.inl (hJO x hx)) (fun x hx => ⟨Or.inl (hSO x hx).1,(hSO x hx).2⟩)
      jsep K Pd NB hK0 hPd0 hNB0 safe hOS hkoWs (fun x hx => hWsP0 x (by omega)) (fun x hx => hsub x (hJE x hx))
      (fun x hx => hsub x (hSE x hx)) h0 ECH hECH (fun x hx => ⟨Or.inl (hW40 x hx).1,hWJ40 x hx⟩)
      (fun x hx => ⟨Or.inl (hW72 x hx).1,hWJ72 x hx⟩) Wbal BV BVo
      (fun x hx => let k := hWb x hx; ⟨Or.inl k.1,k.2⟩) hBVf
      (hBVf M0 Mp hBV0 (fun x hx => fr x (hWb x hx).1 (fun e => (hWb x hx).2.1 (hsub x e)))) (hinc Y Hp Mp Hb) orc
      ⟨⟨Or.inr ⟨by omega,by omega⟩,fun h => by
          rcases h with h | h
          · have := hExclP0 _ h; omega
          · have := (hOutSafe _ (hWb _ h).1).2; omega⟩,
        ⟨Or.inr ⟨by omega,by omega⟩,fun h => by
          rcases h with h | h
          · have := hExclP0 _ h; omega
          · have := (hOutSafe _ (hWb _ h).1).2; omega⟩⟩ (hRet Y Mp Hb))

#print axioms processTx_pmcX_to_end
end c98
section c1
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 k40 : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- The actual `process_transaction` body (spine drop 1 to `return 0`) with the interpreter output record threaded:
the named staging contracts are `PmcCX` (interpreter) and `IncorpCO` (`incorporate_tx_into_block()` at the reachable
suffix state); the transaction-entry block lists and the return relation are explicit. -/
theorem processTx_fullO {QM : Mem → GA → Prop} (Ix Arr Rarr L40 L72 : BitVec 64)
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
    (Wbal : BitVec 64 → Prop) (BV BVo : Mem → Prop)
    (hWb : ∀ x, Wbal x → Out x ∧ ¬ Excl' x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hBVf : ∀ M M', BV M → (∀ x, Wbal x → M' x = M x) → BV M') (hBV0 : BV M0)
    (hinc : ∀ (Y Hp : BitVec 64) (Mp : Mem) (Hb : BitVec 64), IncorpCO D B w RR SP0 Hp FM G0 J C SKB Bo U Sc n c T
      (fun x => Out x ∨ ORec Y x) ko (fun x => Excl' x ∨ Wbal x) W40 W72 BV BVo Mp Y Ix Hb L40 L72)
    (hRet : ∀ (Y : BitVec 64) (Mp : Mem) (Hb Hg : BitVec 64) L M G,
      (LPSo Y Ix L ∧ PZ n c T (fun x => Out x ∨ ORec Y x) ko D B (fun x => Excl' x ∨ Wbal x) Hb Hg Mp M G) ∧
        BL2 W40 W72 Hb L40 L72 M G ∧ BVo M → RR (.val (.word 0#64)) M G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction)) :=
  processTx_to_pmcS Ix Arr hF (by omega) hcap hSc0 hwSc hScE scSafe hkoSc hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8 hE8
    hw8 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0
    safe hOutSafe hkoWs hJE hSE ne40 hc40 hU hwWS hWO hWE hWsP0
    (processTx_pmcX_to_end Ix Rarr L40 L72 pcx hF hDF hcap ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit
      hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE hBoC hR32D hR32O hR32E hRarr
      hRO0 hRE0 hRw0 hRO8 hRE8 hRw8 hWsP0 hExclP0 hsub hW40 hW72 hdis hB40 hB72 hL40 hL72 hWJ40 hWJ72 ECH hECH Wbal BV
      BVo hWb hBVf hBV0 hinc hRet)

#print axioms processTx_fullO
end c1
end InitECandidate.Runtime
