import InitECandidate.Runtime.PtRecPreGD
import InitECandidate.Runtime.OriginalWsGetAccountCode
/-!
The actual `get_pre_tx_account(addr)`: the read-only cache lookup in the block pre-state account table (`bs + 16`;
a hit returns the cached record), else `record_pre_state_read(addr)` (registry with owned region, `RegTR`) and the
witness reader `ws_get_account_optional(addr)` (the OPEN contract `WsReadObl`). Every return re-establishes the
registry and the witness invariant at the exit heap; memory below the entry heap changes only in the registry and
witness regions.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exit of a pre-state read: registry and witness invariant re-established at the exit heap, the block-access-list
globals and the journal counter kept, memory below the entry heap changed only in the two regions. -/
def GPPost (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (D : BitVec 64 → Prop) (B : Bool)
    (ko : Fin n) (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop) (BA IA IS KB Ix : BitVec 64)
    (Rr Ow : BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ (H2 H' : BitVec 64) (Ow' : BitVec 64 → Prop), HeapIs G H' ∧ H.toNat ≤ H2.toNat ∧ H2.toNat ≤ H'.toNat ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G ∧
    RegTR n c T Out H' M D B ko (fun x => Rr x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H2.toNat)) ∧ WsI M H' Ow' ∧
    (∀ x, Ow' x → Ow x ∨ (H2.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
    ∀ x, x.toNat < H.toNat → ¬ Rr x → ¬ Ow x → M x = M1 x

theorem shape2r {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one,.one]) = true) :
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a),.val (.word b)] := by
  rcases v with ⟨⟨x⟩⟩ | fs | ⟨n,fs⟩
  · simp [shapeOfHOLExact,shapeEqHOL] at h
  · rcases fs with _ | ⟨⟨⟨a⟩⟩ | _ | _,_ | ⟨⟨⟨b⟩⟩ | _ | _,_ | ⟨_,_⟩⟩⟩ <;>
      simp_all [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
  · simp [shapeOfHOLExact,shapeEqHOL] at h

theorem balG_of_nh {BA IA IS KB Ix : BitVec 64} {G G' : GA} (h : BalG BA IA IS KB Ix G) (nh : GlobNH G G') :
    BalG BA IA IS KB Ix G' := by
  obtain ⟨a,b,c,d,e⟩ := h
  exact ⟨(nh _ (by decide)).trans a,(nh _ (by decide)).trans b,(nh _ (by decide)).trans c,(nh _ (by decide)).trans d,
    (nh _ (by decide)).trans e⟩

section gp
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kB : Fin n}

theorem getPreAcct_aqgd (bk : BalKeep) (BA IA IS KB Ix : BitVec 64)
    (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop)
    (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) (A H Nj : BitVec 64) (Rr Ow : BitVec 64 → Prop) (M1 : Mem) (G1 : GA)
    (reg : RegTR n c T Out H M1 D B ko Rr) (rB : ∀ x, Rr x → x.toNat < H.toNat) (dRO : ∀ x, Ow x → ¬ Rr x)
    (hH1 : HeapIs G1 H) (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (hB1 : BalG BA IA IS KB Ix G1) (wi : WsI M1 H Ow)
    (p0 : P0.toNat ≤ H.toNat) (hwP : w.toNat < P0.toNat) (hwR : ¬ Rr w) (hwO : ¬ Ow w) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => (∃ y : BitVec 64, v = .val (.word y)) ∧
        GPPost n c T Out D B ko WsI BA IA IS KB Ix Rr Ow H Nj M1 M G)
      (sourceFunctionBody Guest.guestFn_get_pre_tx_account) := by
  have hwH : w.toNat < H.toNat := by omega
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_get_pre_tx_account,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  let LA : GA → Prop := fun L => L.lookup (ofString "addr") = some (.val (.word A))
  have post0 : GPPost n c T Out D B ko WsI BA IA IS KB Ix Rr Ow H Nj M1 M1 G1 :=
    ⟨H,H,Ow,hH1,le_refl _,le_refl _,hn1,hB1,regTR_sub reg (fun x h => Or.inl h),wi,fun x h => Or.inl h,
      fun _ _ _ _ => rfl⟩
  -- w = htab_get(lds (bs + 16), addr): read-only
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => (LA L ∧ ∃ a b : BitVec 64,
      L.lookup (ofString "w") = some (.rStruct [.val (.word a),.val (.word b)])) ∧ M = M1 ∧ G = G1)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _
    originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨la,hM,hG⟩ ⟨e1,e2⟩ sh
    subst e1 e2
    obtain ⟨a,b,rfl⟩ := shape2r sh
    exact ⟨⟨by show _ = _; rw [lookup_update_ne' _ _ (by decide)]; exact la,a,b,lookup_update_eq' _ _ _⟩,hM,hG⟩
  refine aqgd_seq (Q := fun L M G => LA L ∧ M = M1 ∧ G = G1) (aqgd_ite (CT := fun _ _ _ => True)
      (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_return _ (fun s v H' _ hG ⟨⟨⟨_,a,b,hw⟩,hM,hG1⟩,_⟩ _ ev => ?_))
      (aqgd_conseq aqgd_skip (fun L M G h => ⟨h.1.1.1,h.1.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · simp [EV,evalHOLExact,hw] at ev
    unfold GIs at hG; subst hG
    rw [hM,hG1]
    exact ⟨⟨b,ev.symm⟩,post0⟩
  -- record_pre_state_read(addr)
  refine aqgd_seq (Q := fun L M G => LA L ∧ RPPost n c T Out D B ko Rr H Nj M1 M G ∧ BalG BA IA IS KB Ix G)
    (aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_callSpecD (Vn' := fun _ => False)
        (P := fun L M G => LA L ∧ M = M1 ∧ G = G1)
        (Q := fun L M G => LA L ∧ RPPost n c T Out D B ko Rr H Nj M1 M G)
        (Pe := fun _ M0' _ L M G => (∃ A' : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A'))) ∧
          RegTR n c T Out H M D B ko Rr ∧ M = M0' ∧ HeapIs G H ∧
          G.lookup (ofString "journal_n") = some (.val (.word Nj)))
        (RRe := fun _ M0' _ _ M' G' => RPPost n c T Out D B ko Rr H Nj M0' M' G')
        _ _ _ _ _ originalRuntimeCode_recordPreStateRead_lookup (by simp) ?_ ?_ ?_))
      (fun L M G h => ⟨h,by rw [h.2.2]; exact hB1⟩) (fun L M G ⟨⟨la,po⟩,bg⟩ => ⟨la,po,bg⟩) (fun _ _ _ h => h.1)) ?_
  · intro L0 M0' G0' _
    exact aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (recordPreR_aqgd (M0 := M0') (J := J) (C := C) (SKB := SKB)
        ne hBs hcB p0 hwP hwR)
      (keepsBo_of_installed originalRuntimeCode_recordPreStateRead_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_recordPreStateRead_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_recordPreStateRead_lookup (by decide))
  · intro F s values callee rs _ _ G hG ⟨la,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    have la' : s.locals.lookup (ofString "addr") = some (.val (.word A)) := la
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,la'] at args
    subst args
    have e := callee_eq originalRuntimeCode_recordPreStateRead_lookup lookup
    refine ⟨⟨A,by rw [e]; simp (config := {decide := true})⟩,by rw [hM]; exact reg,rfl,by rw [hG1]; exact hH1,
      by rw [hG1]; exact hn1⟩
  · intro L M G v M' G' ⟨la,hM,_⟩ po
    subst hM
    exact ⟨la,po⟩
  -- a = ws_get_account_optional(addr); return a
  refine aqgd_conseq (P := fun L M G => ∃ H2 : BitVec 64, LA L ∧ ((HeapIs G H2 ∧ H.toNat ≤ H2.toNat ∧
      RegTR n c T Out H2 M D B ko (fun x => Rr x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H2.toNat)) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∀ x, x.toNat < H.toNat → ¬ Rr x → M x = M1 x) ∧ BalG BA IA IS KB Ix G))
    (aqgd_ex (fun H2 => aqgd_ghostR (fun M3 G3 ⟨⟨hH3,le3,reg3,hn3,fr3⟩,bg3⟩ => ?_)))
    (fun L M G ⟨la,⟨H2,hH2,le2,reg2,hn2,fr2⟩,bg⟩ => ⟨H2,la,⟨hH2,le2,reg2,hn2,fr2⟩,bg⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)
  have wi3 : WsI M3 H2 Ow := wsr.1.1 M1 H Ow M3 H2 wi (fun x hx => fr3 x (wsr.1.2 M1 H Ow wi x hx) (dRO x hx)) le3
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => LA L ∧ M = M0' ∧ G = G0')
    (RRe := fun _ _ _ v M' G' => ∃ (H' : BitVec 64) (Ow' : BitVec 64 → Prop), HeapIs G' H' ∧
      H2.toNat ≤ H'.toNat ∧ GlobNH G3 G' ∧ WsI M' H' Ow' ∧
      (∀ x, Ow' x → Ow x ∨ (H2.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
      (∀ x, x.toNat < H2.toNat → ¬ Ow x → M' x = M3 x) ∧ ∃ y : BitVec 64, v = .val (.word y))
    (Pc := fun L M G => ∃ y : BitVec 64, L.lookup (ofString "a") = some (.val (.word y)) ∧
      GPPost n c T Out D B ko WsI BA IA IS KB Ix Rr Ow H Nj M1 M G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_wsGetAccount_lookup (by simp)
    (fun L0 M0' G0' ⟨_,hM,hG⟩ => by
      rw [hM,hG]
      exact wsr.2.1 A w M3 G3 H2 Ow wi3 hH3 hwO (by omega)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ _ G hG ⟨la,_,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    have la' : s.locals.lookup (ofString "addr") = some (.val (.word A)) := la
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,la'] at args
    subst args
    have e := callee_eq originalRuntimeCode_wsGetAccount_lookup lookup
    exact ⟨by show _ = _; rw [e]; simp (config := {decide := true}),rfl,rfl⟩
  · intro L M G v M' G' ⟨_,hM,hG⟩ ⟨H',Ow',hH',le',nh,wi',sub',frW,y,hv⟩ _
    subst hM hG hv
    refine ⟨y,lookup_update_eq' _ _ _,H2,H',Ow',hH',le3,le',(nh _ (by decide)).trans hn3,balG_of_nh bg3 nh,
      regTR_mono (regTR_frame reg3 (fun x hx => frW x ?_ ?_)) le',wi',sub',
      fun x hx hR hO => (frW x (by omega) hO).trans (fr3 x hx hR)⟩
    · rcases hx with h | ⟨_,h⟩
      · have := rB x h; omega
      · exact h
    · intro hO
      rcases hx with h | ⟨h1,_⟩
      · exact dRO x hO h
      · have := wsr.1.2 M1 H Ow wi x hO; omega
  exact aqgd_return _ (fun s v H' _ hG ⟨y,hy,po⟩ _ ev => by
    simp [EV,evalHOLExact,hy] at ev
    unfold GIs at hG; subst hG
    exact ⟨⟨y,ev.symm⟩,po⟩)

#print axioms getPreAcct_aqgd

end gp
end InitECandidate.Runtime
