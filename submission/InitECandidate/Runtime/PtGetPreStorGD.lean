import InitECandidate.Runtime.PtGetPreGD
/-!
The actual `get_pre_tx_storage(addr, key)`: the read-only cached lookup `stor_lookup(lds (bs + 32), addr, key)` (a hit
returns the cached value), else `record_pre_state_read(addr)` over `RegTR` and the witness reader
`ws_get_storage(addr, key)` (OPEN `WsReadObl`); every return satisfies `GPPost`. The installed-code equations of
`stor_lookup` and `ws_get_storage` are explicit hypotheses (decidable lookup facts, root lemmas pending).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section gs
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kB : Fin n}

theorem getPreStor_aqgd (bk : BalKeep) (BA IA IS KB Ix : BitVec 64)
    (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop)
    (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64)
    (instSL : originalRuntimeCode.lookup (ofString "stor_lookup") = some ([(ofString "outer",.one),
      (ofString "addr",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_stor_lookup,.comb [.one,.one]))
    (instWS : originalRuntimeCode.lookup (ofString "ws_get_storage") = some ([(ofString "addr",.one),
      (ofString "key",.one)],sourceFunctionBody Guest.guestFn_ws_get_storage,.comb [.one,.one,.one,.one]))
    (A K H Nj : BitVec 64) (Rr Ow : BitVec 64 → Prop) (M1 : Mem) (G1 : GA)
    (reg : RegTR n c T Out H M1 D B ko Rr) (rB : ∀ x, Rr x → x.toNat < H.toNat) (dRO : ∀ x, Ow x → ¬ Rr x)
    (hH1 : HeapIs G1 H) (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (hB1 : BalG BA IA IS KB Ix G1) (wi : WsI M1 H Ow)
    (p0 : P0.toNat ≤ H.toNat) (hwP : w.toNat < P0.toNat) (hwR : ¬ Rr w) (hwO : ¬ Ow w) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (L.lookup (ofString "addr") = some (.val (.word A)) ∧
        L.lookup (ofString "key") = some (.val (.word K))) ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun _ M G => GPPost n c T Out D B ko WsI BA IA IS KB Ix Rr Ow H Nj M1 M G)
      (sourceFunctionBody Guest.guestFn_get_pre_tx_storage) := by
  have hwH : w.toNat < H.toNat := by omega
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_get_pre_tx_storage,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  let LA : GA → Prop := fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
    L.lookup (ofString "key") = some (.val (.word K))
  have post0 : GPPost n c T Out D B ko WsI BA IA IS KB Ix Rr Ow H Nj M1 M1 G1 :=
    ⟨H,Ow,hH1,le_refl _,hn1,hB1,regTR_sub reg (fun x h => Or.inl h),wi,fun x h => Or.inl h,fun _ _ _ _ => rfl⟩
  -- w = htab_get(lds (bs + 16), addr): read-only
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => LA L ∧ M = M1 ∧ G = G1)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _
    instSL (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf (memoryFrame_of_good instSL (by decide) (by decide))
      (by body_check Guest.guestFn_stor_lookup) (by body_check Guest.guestFn_stor_lookup) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨la,lk⟩,hM,hG⟩ ⟨e1,e2⟩ _
    subst e1 e2
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact la,by rw [lookup_update_ne' _ _ (by decide)]; exact lk⟩,
      hM,hG⟩
  refine aqgd_seq (Q := fun L M G => LA L ∧ M = M1 ∧ G = G1) (aqgd_ite (CT := fun _ _ _ => True)
      (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_return _ (fun s v H' _ hG ⟨⟨_,hM,hG1⟩,_⟩ _ _ => ?_))
      (aqgd_conseq aqgd_skip (fun L M G h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · unfold GIs at hG; subst hG
    rw [hM,hG1]
    exact post0
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
    have la' : s.locals.lookup (ofString "addr") = some (.val (.word A)) := la.1
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
      (∀ x, x.toNat < H2.toNat → ¬ Ow x → M' x = M3 x) ∧
      ∃ a b c d : BitVec 64, v = .rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)])
    (Pc := fun _ M G => GPPost n c T Out D B ko WsI BA IA IS KB Ix Rr Ow H Nj M1 M G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ instWS (by simp)
    (fun L0 M0' G0' ⟨_,hM,hG⟩ => by
      rw [hM,hG]
      exact wsr.2.2 A K w M3 G3 H2 Ow wi3 hH3 hwO (by omega)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ _ G hG ⟨la,_,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    have la' : s.locals.lookup (ofString "addr") = some (.val (.word A)) := la.1
    have lk' : s.locals.lookup (ofString "key") = some (.val (.word K)) := la.2
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,la',lk'] at args
    subst args
    have e := callee_eq instWS lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨_,hM,hG⟩ ⟨H',Ow',hH',le',nh,wi',sub',frW,_⟩ _
    subst hM hG
    refine ⟨H',Ow',hH',by omega,(nh _ (by decide)).trans hn3,balG_of_nh bg3 nh,
      regTR_sub (regTR_mono (regTR_frame reg3 (fun x hx => frW x ?_ ?_)) le') ?_,wi',?_,
      fun x hx hR hO => (frW x (by omega) hO).trans (fr3 x hx hR)⟩
    · rcases hx with h | ⟨_,h⟩
      · have := rB x h; omega
      · exact h
    · intro hO
      rcases hx with h | ⟨h1,_⟩
      · exact dRO x hO h
      · have := wsr.1.2 M1 H Ow wi x hO; omega
    · intro x h
      rcases h with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1,by omega⟩
    · intro x h
      rcases sub' x h with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega,h2⟩
  exact aqgd_return _ (fun s v H' _ hG po _ _ => by
    unfold GIs at hG; subst hG
    exact po)

#print axioms getPreStor_aqgd
end gs
end InitECandidate.Runtime
