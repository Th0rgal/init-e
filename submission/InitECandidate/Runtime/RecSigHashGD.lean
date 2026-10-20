import InitECandidate.Runtime.RecSecpRecoverGD
import InitECandidate.Runtime.ScrGlobalKeep
/-!
`keccak256` over the pinned-journal arena (static `keccak_st` / `keccak_pad` from `G0`), `ScrIs` kept by every
`goodScr` body (`aqgd_keepScr`), and the window spec of the actual `tx_signing_hash_mode(tx, mode, chain_id, out)`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem jwsn_keccak {SP0 P0 FM J C SKB Nj K Pd : BitVec 64} {G0 g : GA}
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (h : JWSN SP0 P0 FM G0 J C SKB Nj g) :
    g.lookup (ofString "keccak_st") = some (.val (.word K)) ∧ g.lookup (ofString "keccak_pad") = some (.val (.word Pd)) :=
  ⟨(h.1.1.1.2.2.2 _ (by decide)).1.trans hK0,(h.1.1.1.2.2.2 _ (by decide)).1.trans hPd0⟩

/-- A two-word value. -/
def U2V (v : ValueHOL 64) : Prop := ∃ a b : BitVec 64, v = .rStruct [.val (.word a),.val (.word b)]

theorem u2v_of_check {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one,.one]) = true) : U2V v := by
  have h' := (shapeEqHOL_eq_true _ _).mp h
  cases v with
  | val x => simp [shapeOfHOLExact] at h'
  | nStruct n fs => simp [shapeOfHOLExact] at h'
  | rStruct fs =>
    simp [shapeOfHOLExact] at h'
    rcases fs with _ | ⟨v1,_ | ⟨v2,_ | ⟨v3,fs⟩⟩⟩ <;> simp at h'
    obtain ⟨h1,h2⟩ := h'
    obtain ⟨a,rfl⟩ := word_of_shape_one h1
    obtain ⟨b,rfl⟩ := word_of_shape_one h2
    exact ⟨a,b,rfl⟩

#print axioms u2v_of_check

section kg
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- `keccak256` over the pinned-journal arena, keeping any globals predicate. -/
theorem keccakGP (K Pd : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (oK : ¬ MWin K 200 w)
    (oP : ¬ MWin Pd 136 w) (O : BitVec 64) (oO : ¬ MWin O 32 w) (GP : GA → Prop) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (∃ Pp N : BitVec 64, KL0 Pp N O L) ∧ GP G) (fun _ _ _ => True) (fun _ _ G => True ∧ GP G)
      (sourceFunctionBody Guest.guestFn_keccak256) :=
  aqgd_conseq (aqgd_keepGI (GI := GP) (keepsGA_of_installed originalRuntimeCode_keccak_lookup (by decide))
    (aqgd_exE (fun Pp => aqgd_exE (fun N => keccak_wn K Pd (fun g h => jwsn_keccak hK0 hPd0 h) Pp N O oK oP oO))))
    (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

#print axioms keccakGP
end kg

section ks
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A body keeping `secp_accel_scratch` keeps `ScrIs`. -/
theorem aqgd_keepScr {Sc : BitVec 64} {P Q : GA → Mem → GA → Prop} {body : ProgHOL 64}
    (hk : keepsG (ofString "secp_accel_scratch") goodScr body = true) (h : AQGD D B A w Vn P Q RR body) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ ScrIs Sc G) (fun L M G => Q L M G ∧ ScrIs Sc G)
      (fun v M G => RR v M G ∧ ScrIs Sc G) body := by
  intro F s code dom aw sl H hH ⟨pre,g⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH pre
  have glob := evaluate_keeps_scr body hk s code
  unfold GIs at hH; subst hH
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',H',hH',q⟩ := n e
    unfold GIs at hH'
    exact ⟨sl',H',hH',q,by unfold ScrIs; rw [← hH',glob]; exact g⟩
  · obtain ⟨H',hH',rr⟩ := r v e
    unfold GIs at hH'
    exact ⟨H',hH',rr,by unfold ScrIs; rw [← hH',glob]; exact g⟩

#print axioms aqgd_keepScr
end ks

def shmBody : ProgHOL 64 :=
  (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "e") (.comb [.one,.one]) (ofString "tx_encode_generic") [(.var .local (ofString "tx")),(.var .local (ofString "mode")),(.var .local (ofString "chain_id"))] (.seq (.call (some (none,none)) (ofString "keccak256") [(.rfield 0 (.var .local (ofString "e"))),(.rfield 1 (.var .local (ofString "e"))),(.var .local (ofString "out"))]) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.const 0))))))

theorem shmBody_eq : sourceFunctionBody Guest.guestFn_tx_signing_hash_mode = shmBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_tx_signing_hash_mode,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

section sh
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat}

/-- The actual `tx_signing_hash_mode(tx, mode, chain_id, out)`: `tx_encode_generic` writes only above the heap pointer
(explicit domain fence), `keccak256` writes only its state, pad and `[O, O + 32)`; the heap is released; keeps `RG`. -/
theorem sigHashMode_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "out") = some (.val (.word O)) ∧
        ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))) ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_tx_signing_hash_mode) := by
  rw [shmBody_eq]; unfold shmBody
  let LS := fun L : GA => L.lookup (ofString "out") = some (.val (.word O)) ∧
    ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))
  have lsu : ∀ (n : MlS), ofString "out" ≠ n → ofString "chain_id" ≠ n → ∀ L v, LS L → LS (L.update (n,v)) :=
    fun n h1 h2 L v ⟨ho,c,hc⟩ => ⟨by rw [lookup_update_ne' _ _ h1]; exact ho,c,by rw [lookup_update_ne' _ _ h2]; exact hc⟩
  refine aqgd_conseq (P := fun L _ G => ∃ H : BitVec 64, ((LS L ∧ HeapIs G H) ∧ ScrIs Sc G) ∧ Lo.toNat ≤ H.toNat)
    (Q := fun _ _ _ => False) ?_ (fun _ _ _ ⟨ls,⟨H,hH,le⟩,hs⟩ => ⟨H,⟨⟨ls,hH⟩,hs⟩,le⟩) (fun _ _ _ h => h.elim)
    (fun _ _ _ h => h)
  refine aqgd_exE (fun H => ?_)
  refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
    (fun _ _ g aw ⟨⟨⟨_,hH⟩,_⟩,_⟩ => jws_heap_facts aw.1 hH) ?_
  intro ⟨hP0,hcapH,hal⟩
  refine aqgd_pureE (fun hLoH => ?_)
  -- mark = heap_mark()
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      v = .val (.word H) ∧ M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => ((LS L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧ HeapIs G H) ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_heap_mark_lookup
    (fun _ M0' G0' ⟨⟨_,hH⟩,_⟩ => heapMark_spec M0' G0' H hH) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨ls,hH⟩,hs⟩ ⟨ev,_,hG⟩ _
    subst ev hG
    exact ⟨⟨⟨lsu _ (by decide) (by decide) _ _ ls,lookup_update_eq' _ _ _⟩,hH⟩,hs⟩
  -- e = tx_encode_generic(tx, mode, chain_id)
  let LE := fun L : GA => (LS L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
    ∃ v, L.lookup (ofString "e") = some v ∧ U2V v
  refine aqgd_decCallSpecS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ G => ((∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))) ∧
      HeapIs G H) ∧ ScrIs Sc G)
    (RRe := fun _ _ _ _ _ G => HGe H G ∧ ScrIs Sc G)
    (Pc := fun L _ G => LE L ∧ HGe H G ∧ ScrIs Sc G) (Qc := fun _ _ _ => False) _ _ _ _ _ _ _
    originalRuntimeCode_txEncodeGeneric_lookup (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ => aqgd_conseq (aqgd_keepScr (Sc := Sc)
      (keepsScr_of_installed originalRuntimeCode_txEncodeGeneric_lookup (by decide))
      (encGeneric_win (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB) (Nj := Nj)
        (B := B) hF hDF hcap H (by omega))) (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h))
    ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H' hG ⟨⟨⟨⟨_,c,hc⟩,_⟩,hH⟩,hs⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,hc] at ev3; subst ev3
    have e := callee_eq originalRuntimeCode_txEncodeGeneric_lookup lookup
    exact ⟨⟨⟨c,by rw [e]; simp (config := {decide := true})⟩,hH⟩,hs⟩
  · intro L M G v M' G' ⟨⟨⟨ls,hm⟩,_⟩,_⟩ ⟨hge,hs⟩ ok
    exact ⟨⟨⟨lsu _ (by decide) (by decide) _ _ ls,by rw [lookup_update_ne' _ _ (by decide)]; exact hm⟩,v,
      lookup_update_eq' _ _ _,u2v_of_check ok⟩,hge,hs⟩
  -- keccak256(e.0, e.1, out)
  refine aqgd_seq (rcallK (GP := fun G => HGe H G ∧ ScrIs Sc G) (LP := LE) (Rv := fun _ => True)
    (fun L => ∃ Pp N : BitVec 64, KL0 Pp N O L) _ _ _ _ _ originalRuntimeCode_keccak_lookup
    (keccakGP K Pd hK0 hPd0 oK oP O oO _)
    (fun s values callee rs ⟨⟨⟨ho,_⟩,_⟩,u,hu,a,b,hab⟩ args lookup => by
      subst hab
      obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,hu] at ev1 ev2; subst ev1 ev2
      simp [EV,evalHOLExact,ho] at ev3; subst ev3
      have e := callee_eq originalRuntimeCode_keccak_lookup lookup
      exact ⟨a,b,by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),
        by rw [e]; simp (config := {decide := true})⟩)) ?_
  -- heap_release(mark); return 0
  refine aqgd_seq (Q := fun _ _ G => HeapIs G H ∧ ScrIs Sc G) (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "m") = some (.val (.word H)) ∧ M = M0') ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (M' = M0' ∧ HeapIs G' H) ∧ OnlyHeap G0' G')
    _ _ _ _ _ originalRuntimeCode_heap_release_lookup (by simp)
    (fun _ M0' G0' _ => heapReleaseN_spec (SP0 := SP0) (G0 := G0) (FM := FM) (J := J) (C := C) (SKB := SKB) (Nj := Nj)
      (D := D) (B := B) (w := w) M0' H hP0 hcapH hal G0') ?_ ?_) (aqgd_return _ ?_)
  · intro F s values callee rs _ H' hG ⟨⟨⟨_,hm⟩,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,hm] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_heap_release_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩,rfl⟩
  · intro L M G v M' G' ⟨_,_,hs⟩ ⟨⟨_,hH⟩,oh⟩
    exact ⟨hH,scrIs_onlyHeap oh hs⟩
  · intro F s v _ _ _ ⟨hH,hs⟩ _ _
    exact ⟨⟨H,hH,hLoH⟩,hs⟩

#print axioms sigHashMode_wn
end sh
end InitECandidate.Runtime
