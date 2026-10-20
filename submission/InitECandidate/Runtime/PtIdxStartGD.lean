import InitECandidate.Runtime.PtIdxRecGD
/-!
The actual `idx_start_account(addr)` body in the block-access-list builder world, and the world-level declared call
of `get_pre_tx_account`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section is
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko kB : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop} {Sk : BitVec 64 → Prop}
  {Nj : BitVec 64}

/-- The world-level declared call `name = get_pre_tx_account(ea)`. -/
theorem aqgd_decCall_gpaW (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (ea : ExpHOL 64)
    {cont : ProgHOL 64} (A : BitVec 64) {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64}
    {Rr Ow : BitVec 64 → Prop} {M2 : Mem} {G2 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 G2)
    (p0 : P0.toNat ≤ H.toNat) (hwP : w.toNat < P0.toNat) (hwR : ¬ Rr w) (hwO : ¬ Ow w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M2 → s.globals = G2 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea] =
        some [.val (.word A)])
    (hres : ∀ (L : GA) (y : BitVec 64) (M : Mem) (G : GA), LP L →
      USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 M G → Pc (L.update (name,.val (.word y))) M G)
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2) Q RR
      (.decCall name .one (ofString "get_pre_tx_account") [ea] cont) := by
  have u' := u
  obtain ⟨hH,hn,bg,_,reg,wi,rB,dRO,_⟩ := u'
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ _ _ v M' G' => (∃ y : BitVec 64, v = .val (.word y)) ∧
      GPPost n c T Out D B ko WsI BA IA IS KB Ix Rr Ow H Nj M2 M' G')
    _ _ _ _ _ _ _ originalRuntimeCode_getPreTxAccount_lookup (by simp)
    (fun L0 M0' G0' ⟨_,hM,hG⟩ => by
      rw [hM,hG]
      exact aqgd_conseq (getPreAcct_aqgd bk BA IA IS KB Ix WsI wsr ne Bs hBs hcB A H Nj Rr Ow M2 G2 reg rB dRO hH hn bg
        wi p0 hwP hwR hwO) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ hc
    (fun L _ _ L' M' G' ⟨lp,_,_⟩ q => hq L L' M' G' lp q)
  · intro F s values callee rs _ dom H' hG ⟨lp,hM,hG2⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG2 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    have e := callee_eq originalRuntimeCode_getPreTxAccount_lookup lookup
    exact ⟨by rw [e]; simp (config := {decide := true}),rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,_,_⟩ ⟨⟨y,hv⟩,gp⟩ _
    subst hv
    exact hres L y M' G' lp (ust_of_gp wsr.1 u gp)

#print axioms aqgd_decCall_gpaW
/-- The actual `idx_start_account(addr)`: every return gives a word and is a world step. -/
theorem idxStartAcct_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) (A : BitVec 64) {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop}
    {H : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M1 : Mem} {G1 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 G1)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => (∃ y : BitVec 64, v = .val (.word y)) ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 M G)
      (sourceFunctionBody Guest.guestFn_idx_start_account) := by
  refine uw_heapFact u (fun ⟨p0,hHE,_⟩ => ?_)
  have u' := u
  obtain ⟨hH,hn,bg,_⟩ := u'
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_idx_start_account,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  let LPk : GA → Prop := fun L => L.lookup (ofString "kb") = some (.val (.word KB)) ∧
    L.lookup (ofString "addr") = some (.val (.word A))
  refine aqgd_decD (Pb := fun L M G => LPk L ∧ M = M1 ∧ G = G1)
    (Qb := fun _ _ _ => False) (ofString "kb") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ _ hG ⟨la,hM,hG1⟩ _ ev _
    unfold GIs at hG
    have gk : s.globals.lookup (ofString "bal_key_buf") = some (.val (.word KB)) := by
      rw [hG,hG1]; exact bg.2.2.2.1
    simp [EV,evalHOLExact,gk] at ev; subst ev
    exact ⟨⟨lookup_update_eq' _ _ _,by rw [lookup_update_ne' _ _ (by decide)]; exact la⟩,hM,hG1⟩
  refine aqgd_seq (Q := fun L M G => LPk L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 M G)
    (aqgd_stLe64_kbW wsr.1 u hHE (hwk .kb trivial) (fun L h => h.1)) ?_
  refine aqgd_conseq (aqgd_ust (LP' := fun _ => False) (X := fun v => ∃ y : BitVec 64, v = .val (.word y))
    (fun A2 R2 H2 Rr2 Ow2 M2 G2 u2 le2 hk2 hr2 ho2 => ?_) (by omega) hwk hwR hwO)
    (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)
  refine uw_heapFact u2 (fun ⟨p2,hHE2,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => LPk L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A2 R2 H2 Rr2 Ow2 M2 M G)
    (aqgd_memcpy_kbW wsr.1 u2 hHE2 (hk2 .kb trivial) A (fun L h => h)) ?_
  refine aqgd_ust (fun A3 R3 H3 Rr3 Ow3 M3 G3 u3 le3 hk3 hr3 ho3 => ?_) (by omega) hk2 hr2 ho2
  refine uw_heapFact u3 (fun ⟨p3,_,_⟩ => ?_)
  have u3' := u3
  obtain ⟨_,_,bg3,_⟩ := u3'
  -- m = htab_get(bal_idx_accts, kb): read-only
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => (LPk L ∧ ∃ a b : BitVec 64,
      L.lookup (ofString "m") = some (.rStruct [.val (.word a),.val (.word b)])) ∧ M = M3 ∧ G = G3)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨lk,la⟩,hM,hG⟩ ⟨e1,e2⟩ sh
    subst e1 e2
    obtain ⟨a,b,rfl⟩ := shape2r sh
    exact ⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact lk,by rw [lookup_update_ne' _ _ (by decide)]; exact la⟩,
      a,b,lookup_update_eq' _ _ _⟩,hM,hG⟩
  refine aqgd_seq (Q := fun L M G => LPk L ∧ M = M3 ∧ G = G3) (aqgd_ite (CT := fun _ _ _ => True)
      (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_return _ (fun s v H' _ hG ⟨⟨⟨_,a,b,hm⟩,hM,hG3⟩,_⟩ _ ev => ?_))
      (aqgd_conseq aqgd_skip (fun L M G h => ⟨h.1.1.1,h.1.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · simp [EV,evalHOLExact,hm] at ev
    unfold GIs at hG; subst hG
    rw [hM,hG3]
    exact ⟨⟨b,ev.symm⟩,ust_refl u3⟩
  -- pre = get_pre_tx_account(addr)
  refine aqgd_decCall_gpaW bk wsr ne Bs hBs hcB (LP := LPk)
    (Pc := fun L M G => ∃ y : BitVec 64, (LPk L ∧ L.lookup (ofString "pre") = some (.val (.word y))) ∧
      USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A3 R3 H3 Rr3 Ow3 M3 M G)
    (Qc := fun _ _ _ => False) (ofString "pre") _ A u3 p3 hwP hr3 ho3 ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ ⟨_,la⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la]
  · intro L y M G ⟨lk,la⟩ st
    exact ⟨y,⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact lk,by rw [lookup_update_ne' _ _ (by decide)]; exact la⟩,
      lookup_update_eq' _ _ _⟩,st⟩
  refine aqgd_ex (fun y => ?_)
  refine aqgd_conseq (aqgd_ust (LP' := fun _ => False) (X := fun v => ∃ y : BitVec 64, v = .val (.word y))
    (fun A4 R4 H4 Rr4 Ow4 M4 G4 u4 le4 hk4 hr4 ho4 => ?_) (by omega) hk3 hr3 ho3)
    (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)
  exact aqgd_conseq (idxAcctRec_aqgd bk wsr.1 A y u4 hwP hk4 hr4 ho4)
    (fun L M G ⟨⟨⟨lk,la⟩,lp⟩,hM,hG⟩ => ⟨⟨lk,la,lp⟩,hM,hG⟩) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)

#print axioms idxStartAcct_aqgd
end is
end InitECandidate.Runtime
