import InitECandidate.Runtime.RecSigRecGD
/-!
Window specs of the actual `recover_transaction_public_key`, `sender_address_from_public_key` and
`recover_sender_with_chain_id` (`recoverSender_wn`): the recovery writes only the sender `[S, S + 20)`, the static
Keccak buffers, the secp256k1 accelerator scratch and heap blocks at or above its entry heap pointer (released), under
the explicit domain fence for the signing-hash encoder.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rtpBody : ProgHOL 64 :=
  (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "h") .one (ofString "alloc") [(.const 32)] (.decCall (ofString "recid") .one (ofString "signature_recovery_parameters") [(.var .local (ofString "tx")),(.var .local (ofString "chain_id")),(.var .local (ofString "h"))] (.decCall (ofString "ok") .one (ofString "secp256k1_recover") [(.var .local (ofString "h")),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "tx")),(.const 320)])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "tx")),(.const 352)])),(.var .local (ofString "recid")),(.var .local (ofString "out64"))] (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.seq (.ite (.cmp .equal (.var .local (ofString "ok")) (.const 0)) (.raise (ofString "TxErr") (.const 46)) .skip) (.return (.const 0))))))))

theorem rtpBody_eq : sourceFunctionBody Guest.guestFn_recover_transaction_public_key = rtpBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_recover_transaction_public_key,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl


section rt
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat}

/-- Release of the heap back to a mark `H` held in `mark`, keeping a locals predicate. -/
theorem relMark {LP : GA → Prop} (Lo Sc H : BitVec 64) (hP0 : P0.toNat ≤ H.toNat) (hcapH : H.toNat ≤ 33806089496)
    (hal : H.toNat % 8 = 0) (hm : ∀ L, LP L → L.lookup (ofString "mark") = some (.val (.word H)))
    {RR : ValueHOL 64 → Mem → GA → Prop} {GP : GA → Prop} (hGP : ∀ G, GP G → ScrIs Sc G) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ GP G)
      (fun L _ G => LP L ∧ HeapIs G H ∧ ScrIs Sc G) RR
      (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) :=
  aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "m") = some (.val (.word H)) ∧ M = M0') ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (M' = M0' ∧ HeapIs G' H) ∧ OnlyHeap G0' G')
    _ _ _ _ _ originalRuntimeCode_heap_release_lookup (by simp)
    (fun _ M0' G0' _ => heapReleaseN_spec (SP0 := SP0) (G0 := G0) (FM := FM) (J := J) (C := C) (SKB := SKB) (Nj := Nj)
      (D := D) (B := B) (w := w) M0' H hP0 hcapH hal G0')
    (fun s values callee rs _ H' hG ⟨lp,_⟩ _ args lookup => by
      unfold GIs at hG; subst hG
      obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
      simp [EV,evalHOLExact,hm _ lp] at ex
      subst ex
      rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_heap_release_lookup] at lookup
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      obtain ⟨_,rfl,_⟩ := lookup
      exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩,rfl⟩)
    (fun L M G v M' G' ⟨lp,gp⟩ ⟨⟨_,hH⟩,oh⟩ => ⟨lp,hH,scrIs_onlyHeap oh (hGP _ gp)⟩)

#print axioms relMark

/-- Locals of `recover_transaction_public_key`. -/
def RTP (O : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "out64") = some (.val (.word O)) ∧
    ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))

theorem rtp_upd {O : BitVec 64} (n : MlS) (h1 : ofString "out64" ≠ n) (h2 : ofString "chain_id" ≠ n) (L : GA)
    (v : ValueHOL 64) (h : RTP O L) : RTP O (L.update (n,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,let ⟨c,hc⟩ := h.2; ⟨c,by rw [lookup_update_ne' _ _ h2]; exact hc⟩⟩

/-- The actual `recover_transaction_public_key(tx, chain_id, out64)`: the signing hash into a fresh 32-byte heap block,
the public key into `[O, O + 64)`; heap released; keeps `RG`. -/
theorem rtp_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0) (oO : ¬ MWin O 64 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => RTP O L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun _ _ G => RG Lo Sc G)
      (sourceFunctionBody Guest.guestFn_recover_transaction_public_key) := by
  rw [rtpBody_eq]; unfold rtpBody
  refine aqgd_conseq (P := fun L _ G => ∃ H : BitVec 64, ((RTP O L ∧ HeapIs G H) ∧ ScrIs Sc G) ∧ Lo.toNat ≤ H.toNat)
    (Q := fun _ _ _ => False) ?_ (fun _ _ _ ⟨ls,⟨H,hH,le⟩,hs⟩ => ⟨H,⟨⟨ls,hH⟩,hs⟩,le⟩) (fun _ _ _ h => h.elim)
    (fun _ _ _ h => h)
  refine aqgd_exE (fun H => ?_)
  refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
    (fun _ _ g aw ⟨⟨⟨_,hH⟩,_⟩,_⟩ => jws_heap_facts aw.1 hH) ?_
  intro ⟨hP0,hcapH,hal⟩
  refine aqgd_pureE (fun hLoH => ?_)
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      v = .val (.word H) ∧ M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => ((RTP O L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧ HeapIs G H) ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_heap_mark_lookup
    (fun _ M0' G0' ⟨⟨_,hH⟩,_⟩ => heapMark_spec M0' G0' H hH) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨ls,hH⟩,hs⟩ ⟨ev,_,hG⟩ _
    subst ev hG
    exact ⟨⟨⟨rtp_upd _ (by decide) (by decide) _ _ ls,lookup_update_eq' _ _ _⟩,hH⟩,hs⟩
  -- h = alloc(32)
  let RH := fun L : GA => (RTP O L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
    L.lookup (ofString "h") = some (.val (.word H))
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 32#64)) ∧ M = M0' ∧ HeapIs G H) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + (32#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => (RH L ∧ RG Lo Sc G) ∧ H.toNat + 32 ≤ 33806089496)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) 32#64 H M0' G0') ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H' hG ⟨⟨_,hH⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hH⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨ls,hm⟩,_⟩,hs⟩ ⟨⟨ev,_,H',hH',c1,c2⟩,oh⟩ _
    subst ev
    have : (32#64).toNat = 32 := rfl
    exact ⟨⟨⟨⟨rtp_upd _ (by decide) (by decide) _ _ ls,by rw [lookup_update_ne' _ _ (by decide)]; exact hm⟩,
      lookup_update_eq' _ _ _⟩,⟨H',hH',by omega⟩,scrIs_onlyHeap oh hs⟩,by omega⟩
  refine aqgd_pureE (fun hcap32 => ?_)
  have oH : ¬ MWin H 32 w := by simpa using mwin_aboveH (k := 0) hal (by omega) (by omega)
  have rhu : ∀ (n : MlS), ofString "out64" ≠ n → ofString "chain_id" ≠ n → ofString "mark" ≠ n → ofString "h" ≠ n →
      ∀ L v, RH L → RH (L.update (n,v)) := fun n h1 h2 h3 h4 L v ⟨⟨ls,hm⟩,hh⟩ =>
    ⟨⟨rtp_upd n h1 h2 L v ls,by rw [lookup_update_ne' _ _ h3]; exact hm⟩,by rw [lookup_update_ne' _ _ h4]; exact hh⟩
  -- recid = signature_recovery_parameters(tx, chain_id, h)
  refine rdecAny (GP := RG Lo Sc) (LP := RH) (LP' := RH) (SRP H) (ofString "recid") _ _ _ _ _ _
    originalRuntimeCode_signatureRecoveryParameters_lookup
    (sigRecParams_wn hF hDF hcap Lo Sc K Pd H hK0 hPd0 hw oK oP oH)
    (fun s values callee rs ⟨⟨⟨_,c,hc⟩,_⟩,hh⟩ args lookup => by
      obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,hc] at ev2; subst ev2
      simp [EV,evalHOLExact,hh] at ev3; subst ev3
      have e := callee_eq originalRuntimeCode_signatureRecoveryParameters_lookup lookup
      exact ⟨by rw [e]; simp (config := {decide := true}),c,by rw [e]; simp (config := {decide := true})⟩)
    (fun L v rh => rhu _ (by decide) (by decide) (by decide) (by decide) _ _ rh) ?_
  -- ok = secp256k1_recover(h, r, s, recid, out64)
  refine rdecAny (GP := RG Lo Sc) (LP := RH) (LP' := RH) (fun L => L.lookup (ofString "out") = some (.val (.word O)))
    (ofString "ok") _ _ _ _ _ _ originalRuntimeCode_secp256k1Recover_lookup (secpRecover_wn Lo Sc O hw out hSc0 oO)
    (fun s values callee rs ⟨⟨⟨ho,_⟩,_⟩,_⟩ args lookup => by
      obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,_,r3⟩ := evalList_cons' s _ _ _ r2
      obtain ⟨v4,vs4,rfl,_,r4⟩ := evalList_cons' s _ _ _ r3
      obtain ⟨v5,vs5,rfl,ev5,r5⟩ := evalList_cons' s _ _ _ r4
      have := evalList_nil' s _ r5; subst this
      simp [EV,evalHOLExact,ho] at ev5; subst ev5
      have e := callee_eq originalRuntimeCode_secp256k1Recover_lookup lookup
      rw [e]; simp (config := {decide := true}))
    (fun L v rh => rhu _ (by decide) (by decide) (by decide) (by decide) _ _ rh) ?_
  refine aqgd_seq (relMark (LP := RH) Lo Sc H hP0 hcapH hal (fun L h => h.1.2) (fun G h => h.2)) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_raise _ _) aqgd_skip) ?_
  exact aqgd_return _ (fun _ _ _ _ _ ⟨_,hH,hs⟩ _ _ => ⟨⟨H,hH,hLoH⟩,hs⟩)

#print axioms rtp_wn

/-- `memcpy(dst, src, n)` keeping any globals predicate. -/
theorem memcpyGP (Dd N : BitVec 64) (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin Dd N.toNat w) (GP : GA → Prop) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        (∃ S : BitVec 64, L.lookup (ofString "src") = some (.val (.word S))) ∧
        L.lookup (ofString "n") = some (.val (.word N))) ∧ GP G)
      (fun _ _ _ => True) (fun _ _ G => True ∧ GP G) (sourceFunctionBody Guest.guestFn_memcpy) := by
  have h1 : ∀ (S : BitVec 64) (M0 : Mem) (G0' : GA), AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L M G => (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        L.lookup (ofString "src") = some (.val (.word S)) ∧ L.lookup (ofString "n") = some (.val (.word N))) ∧
        M = M0 ∧ G = G0') (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_memcpy) :=
    fun S M0 G0' => aqgd_conseq (memcpy_wn Dd S N small out M0 G0') (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ _ => trivial)
  have h2 : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L M G => ∃ S : BitVec 64, ∃ M0 : Mem, ∃ G0' : GA, (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        L.lookup (ofString "src") = some (.val (.word S)) ∧ L.lookup (ofString "n") = some (.val (.word N))) ∧
        M = M0 ∧ G = G0') (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_memcpy) :=
    aqgd_exE (fun S => aqgd_exE (fun M0 => aqgd_exE (fun G0' => h1 S M0 G0')))
  exact aqgd_conseq (aqgd_keepGI (GI := GP) (keepsGA_of_installed originalRuntimeCode_memcpy_lookup (by decide)) h2)
    (fun L M G ⟨⟨hd,⟨S,hs⟩,hn⟩,g⟩ => ⟨⟨S,M,G,⟨hd,hs,hn⟩,rfl,rfl⟩,g⟩) (fun _ _ _ _ => trivial)
    (fun _ _ _ ⟨_,g⟩ => ⟨trivial,g⟩)

def saBody : ProgHOL 64 :=
  (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "h") .one (ofString "alloc") [(.const 32)] (.seq (.call (some (none,none)) (ofString "keccak256") [(.op .add [(.var .local (ofString "pubkey65")),(.const 1)]),(.const 64),(.var .local (ofString "h"))]) (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "out20")),(.op .add [(.var .local (ofString "h")),(.const 12)]),(.const 20)]) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.const 0)))))))

theorem saBody_eq : sourceFunctionBody Guest.guestFn_sender_address_from_public_key = saBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_sender_address_from_public_key,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def rsBody : ProgHOL 64 :=
  (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "pk") .one (ofString "alloc") [(.const 72)] (.seq (.storeByte (.var .local (ofString "pk")) (.const 4)) (.seq (.call (some (none,none)) (ofString "recover_transaction_public_key") [(.var .local (ofString "tx")),(.var .local (ofString "chain_id")),(.op .add [(.var .local (ofString "pk")),(.const 1)])]) (.seq (.call (some (none,none)) (ofString "sender_address_from_public_key") [(.var .local (ofString "pk")),(.var .local (ofString "out20"))]) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.const 0))))))))

theorem rsBody_eq : sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id = rsBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_recover_sender_with_chain_id,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl


/-- The actual `sender_address_from_public_key(pubkey65, out20)`: Keccak of the key into a fresh 32-byte heap block,
then 20 bytes into `[S, S + 20)`; heap released; keeps `RG`. -/
theorem sa_wn (Lo Sc K Pd S : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oS : ¬ MWin S 20 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => ((∃ Pk : BitVec 64, L.lookup (ofString "pubkey65") = some (.val (.word Pk))) ∧
        L.lookup (ofString "out20") = some (.val (.word S))) ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun _ _ G => RG Lo Sc G)
      (sourceFunctionBody Guest.guestFn_sender_address_from_public_key) := by
  rw [saBody_eq]; unfold saBody
  let SA := fun L : GA => (∃ Pk : BitVec 64, L.lookup (ofString "pubkey65") = some (.val (.word Pk))) ∧
    L.lookup (ofString "out20") = some (.val (.word S))
  have sau : ∀ (n : MlS), ofString "pubkey65" ≠ n → ofString "out20" ≠ n → ∀ L v, SA L → SA (L.update (n,v)) :=
    fun n h1 h2 L v ⟨⟨Pk,hp⟩,ho⟩ => ⟨⟨Pk,by rw [lookup_update_ne' _ _ h1]; exact hp⟩,by rw [lookup_update_ne' _ _ h2]; exact ho⟩
  refine aqgd_conseq (P := fun L _ G => ∃ H : BitVec 64, ((SA L ∧ HeapIs G H) ∧ ScrIs Sc G) ∧ Lo.toNat ≤ H.toNat)
    (Q := fun _ _ _ => False) ?_ (fun _ _ _ ⟨ls,⟨H,hH,le⟩,hs⟩ => ⟨H,⟨⟨ls,hH⟩,hs⟩,le⟩) (fun _ _ _ h => h.elim)
    (fun _ _ _ h => h)
  refine aqgd_exE (fun H => ?_)
  refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
    (fun _ _ g aw ⟨⟨⟨_,hH⟩,_⟩,_⟩ => jws_heap_facts aw.1 hH) ?_
  intro ⟨hP0,hcapH,hal⟩
  refine aqgd_pureE (fun hLoH => ?_)
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      v = .val (.word H) ∧ M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => ((SA L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧ HeapIs G H) ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_heap_mark_lookup
    (fun _ M0' G0' ⟨⟨_,hH⟩,_⟩ => heapMark_spec M0' G0' H hH) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨ls,hH⟩,hs⟩ ⟨ev,_,hG⟩ _
    subst ev hG
    exact ⟨⟨⟨sau _ (by decide) (by decide) _ _ ls,lookup_update_eq' _ _ _⟩,hH⟩,hs⟩
  let SH := fun L : GA => (SA L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
    L.lookup (ofString "h") = some (.val (.word H))
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 32#64)) ∧ M = M0' ∧ HeapIs G H) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + (32#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => (SH L ∧ RG Lo Sc G) ∧ H.toNat + 32 ≤ 33806089496)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) 32#64 H M0' G0') ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H' hG ⟨⟨_,hH⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hH⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨ls,hm⟩,_⟩,hs⟩ ⟨⟨ev,_,H',hH',c1,c2⟩,oh⟩ _
    subst ev
    have : (32#64).toNat = 32 := rfl
    exact ⟨⟨⟨⟨sau _ (by decide) (by decide) _ _ ls,by rw [lookup_update_ne' _ _ (by decide)]; exact hm⟩,
      lookup_update_eq' _ _ _⟩,⟨H',hH',by omega⟩,scrIs_onlyHeap oh hs⟩,by omega⟩
  refine aqgd_pureE (fun hcap32 => ?_)
  have oH : ¬ MWin H 32 w := by simpa using mwin_aboveH (k := 0) hal (by omega) (by omega)
  -- keccak256(pubkey65 + 1, 64, h)
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := SH) (Rv := fun _ => True)
    (fun L => ∃ Pp N : BitVec 64, KL0 Pp N H L) _ _ _ _ _ originalRuntimeCode_keccak_lookup
    (keccakGP K Pd hK0 hPd0 oK oP H oH _)
    (fun s values callee rs ⟨⟨⟨⟨Pk,hp⟩,_⟩,_⟩,hh⟩ args lookup => by
      obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord] at ev1; subst ev1
      simp [EV,evalHOLExact] at ev2; subst ev2
      simp [EV,evalHOLExact,hh] at ev3; subst ev3
      have e := callee_eq originalRuntimeCode_keccak_lookup lookup
      exact ⟨Pk + 1#64,64#64,by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),
        by rw [e]; simp (config := {decide := true})⟩)) ?_
  -- memcpy(out20, h + 12, 20)
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := SH) (Rv := fun _ => True)
    (fun L => L.lookup (ofString "dst") = some (.val (.word S)) ∧
      (∃ Sr : BitVec 64, L.lookup (ofString "src") = some (.val (.word Sr))) ∧
      L.lookup (ofString "n") = some (.val (.word 20#64))) _ _ _ _ _ originalRuntimeCode_memcpy_lookup
    (memcpyGP S 20#64 (by decide) oS _)
    (fun s values callee rs ⟨⟨⟨_,ho⟩,_⟩,hh⟩ args lookup => by
      obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,ho] at ev1; subst ev1
      simp [EV,evalHOLExact,evalListHOLExact,hh,wordOpHOL,wordOp,valueIsWord,valueWord] at ev2; subst ev2
      simp [EV,evalHOLExact] at ev3; subst ev3
      have e := callee_eq originalRuntimeCode_memcpy_lookup lookup
      exact ⟨by rw [e]; simp (config := {decide := true}),⟨H + 12#64,by rw [e]; simp (config := {decide := true})⟩,
        by rw [e]; simp (config := {decide := true})⟩)) ?_
  refine aqgd_seq (relMark (LP := SH) Lo Sc H hP0 hcapH hal (fun L h => h.1.2) (fun G h => h.2)) ?_
  exact aqgd_return _ (fun _ _ _ _ _ ⟨_,hH,hs⟩ _ _ => ⟨⟨H,hH,hLoH⟩,hs⟩)

#print axioms sa_wn

/-- Locals of `recover_sender_with_chain_id`. -/
def RSL (S : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "out20") = some (.val (.word S)) ∧
    ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))

theorem rsl_upd {S : BitVec 64} (n : MlS) (h1 : ofString "out20" ≠ n) (h2 : ofString "chain_id" ≠ n) (L : GA)
    (v : ValueHOL 64) (h : RSL S L) : RSL S (L.update (n,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,let ⟨c,hc⟩ := h.2; ⟨c,by rw [lookup_update_ne' _ _ h2]; exact hc⟩⟩

/-- The actual `recover_sender_with_chain_id(tx, chain_id, out20)` (`RecC` core): writes only the sender
`[S, S + 20)`, the static Keccak buffers `[K, K + 200)` / `[Pd, Pd + 136)`, the accelerator scratch `[Sc, Sc + 448)`, and
heap blocks at or above the entry heap pointer (released); keeps `RG`. The domain fence is an explicit premise. -/
theorem recoverSender_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd S : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0) (oS : ¬ MWin S 20 w)
    {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => RSL S L ∧ RG Lo Sc G)
      Q (fun _ _ G => RG Lo Sc G)
      (sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id) := by
  rw [rsBody_eq]; unfold rsBody
  refine aqgd_conseq (P := fun L _ G => ∃ H : BitVec 64, ((RSL S L ∧ HeapIs G H) ∧ ScrIs Sc G) ∧ Lo.toNat ≤ H.toNat)
    (Q := fun _ _ _ => False) ?_ (fun _ _ _ ⟨ls,⟨H,hH,le⟩,hs⟩ => ⟨H,⟨⟨ls,hH⟩,hs⟩,le⟩) (fun _ _ _ h => h.elim)
    (fun _ _ _ h => h)
  refine aqgd_exE (fun H => ?_)
  refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
    (fun _ _ g aw ⟨⟨⟨_,hH⟩,_⟩,_⟩ => jws_heap_facts aw.1 hH) ?_
  intro ⟨hP0,hcapH,hal⟩
  refine aqgd_pureE (fun hLoH => ?_)
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      v = .val (.word H) ∧ M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => ((RSL S L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧ HeapIs G H) ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_heap_mark_lookup
    (fun _ M0' G0' ⟨⟨_,hH⟩,_⟩ => heapMark_spec M0' G0' H hH) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨ls,hH⟩,hs⟩ ⟨ev,_,hG⟩ _
    subst ev hG
    exact ⟨⟨⟨rsl_upd _ (by decide) (by decide) _ _ ls,lookup_update_eq' _ _ _⟩,hH⟩,hs⟩
  -- pk = alloc(72)
  let RP := fun L : GA => (RSL S L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
    L.lookup (ofString "pk") = some (.val (.word H))
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 72#64)) ∧ M = M0' ∧ HeapIs G H) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + (72#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => (RP L ∧ RG Lo Sc G) ∧ H.toNat + 72 ≤ 33806089496)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) 72#64 H M0' G0') ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H' hG ⟨⟨_,hH⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hH⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨ls,hm⟩,_⟩,hs⟩ ⟨⟨ev,_,H',hH',c1,c2⟩,oh⟩ _
    subst ev
    have : (72#64).toNat = 72 := rfl
    exact ⟨⟨⟨⟨rsl_upd _ (by decide) (by decide) _ _ ls,by rw [lookup_update_ne' _ _ (by decide)]; exact hm⟩,
      lookup_update_eq' _ _ _⟩,⟨H',hH',by omega⟩,scrIs_onlyHeap oh hs⟩,by omega⟩
  refine aqgd_pureE (fun hcap72 => ?_)
  have hpk : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), RP s.locals →
      s.locals.lookup (ofString "pk") = some (.val (.word H)) := fun s h => h.2
  -- st8 pk, 4
  refine aqgd_seq (aqgd_storeByte (Q := fun L _ G => RP L ∧ RG Lo Sc G) _ _ ?_) ?_
  · intro F s _ _ ⟨rp,rg⟩ _
    refine ⟨H,by simp [EV,evalHOLExact,hpk s rp],fun e => ?_,fun _ _ => ⟨rp,rg⟩⟩
    have h1 := align_toNat H
    rw [← e] at h1; omega
  -- recover_transaction_public_key(tx, chain_id, pk + 1)
  have oO1 : ¬ MWin (H + 1#64) 64 w := mwin_aboveH (k := 1) hal (by omega) (by omega)
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := RP) (Rv := fun _ => True) (RTP (H + 1#64)) _ _ _ _ _
    originalRuntimeCode_recoverTransactionPublicKey_lookup
    (aqgd_conseq (rtp_wn hF hDF hcap Lo Sc K Pd (H + 1#64) hK0 hPd0 hw oK oP out hSc0 oO1) (fun _ _ _ h => h)
      (fun _ _ _ h => h) (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs ⟨⟨⟨_,c,hc⟩,_⟩,hp⟩ args lookup => by
      obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,hc] at ev2; subst ev2
      simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord] at ev3; subst ev3
      have e := callee_eq originalRuntimeCode_recoverTransactionPublicKey_lookup lookup
      exact ⟨by rw [e]; simp (config := {decide := true}),c,by rw [e]; simp (config := {decide := true})⟩)) ?_
  -- sender_address_from_public_key(pk, out20)
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := RP) (Rv := fun _ => True)
    (fun L => (∃ Pk : BitVec 64, L.lookup (ofString "pubkey65") = some (.val (.word Pk))) ∧
      L.lookup (ofString "out20") = some (.val (.word S))) _ _ _ _ _
    originalRuntimeCode_senderAddressFromPublicKey_lookup
    (aqgd_conseq (sa_wn Lo Sc K Pd S hK0 hPd0 hw oK oP oS) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs ⟨⟨⟨ho,_⟩,_⟩,hp⟩ args lookup => by
      obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      have := evalList_nil' s _ r2; subst this
      simp [EV,evalHOLExact,hp] at ev1; subst ev1
      simp [EV,evalHOLExact,ho] at ev2; subst ev2
      have e := callee_eq originalRuntimeCode_senderAddressFromPublicKey_lookup lookup
      exact ⟨⟨H,by rw [e]; simp (config := {decide := true})⟩,by rw [e]; simp (config := {decide := true})⟩)) ?_
  refine aqgd_seq (relMark (LP := RP) Lo Sc H hP0 hcapH hal (fun L h => h.1.2) (fun G h => h.2)) ?_
  exact aqgd_return _ (fun _ _ _ _ _ ⟨_,hH,hs⟩ _ _ => ⟨⟨H,hH,hLoH⟩,hs⟩)

#print axioms recoverSender_wn
end rt
end InitECandidate.Runtime
