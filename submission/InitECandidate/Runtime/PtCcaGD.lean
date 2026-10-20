import InitECandidate.Runtime.PtGaPGGD
/-!
The actual `compute_contract_address(addr, nonce, out)` (watched form over the pinned-journal arena): from heap
pointer `H ≥ Lo`, the RLP list `[addr, nonce]` is written into a fresh 64-byte block (fenced cursor writers), hashed
into a fresh 32-byte block, 20 bytes copied to `[out, out + 20)`, and the heap released back to `H`; every word below
`Lo` off the Keccak state/pad windows and off `[out, out + 20)` is kept, and `RG Lo Sc` holds on return.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ccaBody : ProgHOL 64 :=
  (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "buf") .one (ofString "alloc") [(.const 64)] (.dec (ofString "p") .one (.op .add [(.var .local (ofString "buf")),(.const 9)]) (.decCall (ofString "w") .one (ofString "rlp_encode_bytes") [(.var .local (ofString "p")),(.var .local (ofString "addr")),(.const 20)] (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word") [(.var .local (ofString "p")),(.var .local (ofString "nonce"))]) (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.dec (ofString "payload") .one (.op .sub [(.var .local (ofString "p")),(.op .add [(.var .local (ofString "buf")),(.const 9)])]) (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [(.var .local (ofString "payload"))] (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header") [(.op .sub [(.op .add [(.var .local (ofString "buf")),(.const 9)]),(.var .local (ofString "hl"))]),(.var .local (ofString "payload"))]) (.decCall (ofString "h") .one (ofString "alloc") [(.const 32)] (.seq (.call (some (none,none)) (ofString "keccak256") [(.op .sub [(.op .add [(.var .local (ofString "buf")),(.const 9)]),(.var .local (ofString "hl"))]),(.op .add [(.var .local (ofString "payload")),(.var .local (ofString "hl"))]),(.var .local (ofString "h"))]) (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "out")),(.op .add [(.var .local (ofString "h")),(.const 12)]),(.const 20)]) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.const 0))))))))))))))))

theorem ccaBody_eq : sourceFunctionBody Guest.guestFn_compute_contract_address = ccaBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_compute_contract_address,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


/-- A call of a two-word-parameter function proceeds only with two words. -/
theorem entry2_words {f p q : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,.one),(q,.one)],bd,rs0)) {v1 v2 : ValueHOL 64}
    {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (h : lookupCodeHOLFinite originalRuntimeCode.lookup f [v1,v2] = some (body,callee,rs)) :
    ∃ a b : BitVec 64, v1 = .val (.word a) ∧ v2 = .val (.word b) := by
  have hs := lookupCode_shapes inst h
  simp only [List.zip_cons_cons,List.zip_nil_right,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at hs
  obtain ⟨h1,h2⟩ := hs
  obtain ⟨a,rfl⟩ := word_of_shape_one ((shapeEqHOL_eq_true _ _).mp h1).symm
  obtain ⟨b,rfl⟩ := word_of_shape_one ((shapeEqHOL_eq_true _ _).mp h2).symm
  exact ⟨a,b,rfl,rfl⟩

/-- Locals of `compute_contract_address`: word `addr` and `nonce`, `out = O`. -/
def CAL (O : BitVec 64) (L : GA) : Prop :=
  (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
    (∃ Nc : BitVec 64, L.lookup (ofString "nonce") = some (.val (.word Nc))) ∧
    L.lookup (ofString "out") = some (.val (.word O))

theorem cal_upd {O : BitVec 64} (n : MlS) (h1 : ofString "addr" ≠ n) (h2 : ofString "nonce" ≠ n)
    (h3 : ofString "out" ≠ n) (L : GA) (v : ValueHOL 64) (h : CAL O L) : CAL O (L.update (n,v)) :=
  let ⟨⟨A,ha⟩,⟨Nc,hn⟩,ho⟩ := h
  ⟨⟨A,by rw [lookup_update_ne' _ _ h1]; exact ha⟩,⟨Nc,by rw [lookup_update_ne' _ _ h2]; exact hn⟩,
    by rw [lookup_update_ne' _ _ h3]; exact ho⟩


section cw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat}

/-- The tail of `compute_contract_address`: `h = alloc(32)`, Keccak into `h`, 20 bytes to `out`, heap released. -/
theorem ccaTail_wn (Lo Sc K Pd O H H1 : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 20 w) (hP0 : P0.toNat ≤ H.toNat)
    (hcapH : H.toNat ≤ 33806089496) (hal : H.toNat % 8 = 0) (hLoH : Lo.toNat ≤ H.toNat) (hLo1 : Lo.toNat ≤ H1.toNat)
    (hLo8 : Lo.toNat % 8 = 0) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => ((CAL O L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧ HeapIs G H1) ∧ RG Lo Sc G)
      (fun _ _ _ => False) (fun _ _ G => RG Lo Sc G)
      (.decCall (ofString "h") .one (ofString "alloc") [(.const 32)] (.seq (.call (some (none,none)) (ofString "keccak256") [(.op .sub [(.op .add [(.var .local (ofString "buf")),(.const 9)]),(.var .local (ofString "hl"))]),(.op .add [(.var .local (ofString "payload")),(.var .local (ofString "hl"))]),(.var .local (ofString "h"))]) (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "out")),(.op .add [(.var .local (ofString "h")),(.const 12)]),(.const 20)]) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.const 0)))))) := by
  let SH := fun L : GA => (CAL O L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
    L.lookup (ofString "h") = some (.val (.word H1))
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 32#64)) ∧ M = M0' ∧ HeapIs G H1) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H1) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H1.toNat + (32#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => (SH L ∧ RG Lo Sc G) ∧ H1.toNat + 32 ≤ 33806089496)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) 32#64 H1 M0' G0') ?_ (fun h => h.elim) ?_ ?_
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
  · intro L M G v M' G' ⟨⟨⟨cl,hm⟩,_⟩,hs⟩ ⟨⟨ev,_,H',hH',c1,c2⟩,oh⟩ _
    subst ev
    have : (32#64).toNat = 32 := rfl
    exact ⟨⟨⟨⟨cal_upd _ (by decide) (by decide) (by decide) _ _ cl,by rw [lookup_update_ne' _ _ (by decide)]; exact hm⟩,
      lookup_update_eq' _ _ _⟩,⟨H',hH',by omega⟩,scrIs_onlyHeap oh hs.2⟩,by omega⟩
  refine aqgd_pureE (fun hcap32 => ?_)
  have oH : ¬ MWin H1 32 w := mwin_lo hLo8 hLo1 (by omega) hw
  -- keccak256(buf + 9 - hl, payload + hl, h)
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := SH) (Rv := fun _ => True)
    (fun L => ∃ Pp N : BitVec 64, KL0 Pp N H1 L) _ _ _ _ _ originalRuntimeCode_keccak_lookup
    (keccakGP K Pd hK0 hPd0 oK oP H1 oH _)
    (fun s values callee rs ⟨_,hh⟩ args lookup => by
      obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,hh] at ev3; subst ev3
      obtain ⟨a,b,_,rfl,rfl,_⟩ := entry3_words originalRuntimeCode_keccak_lookup lookup
      have e := callee_eq originalRuntimeCode_keccak_lookup lookup
      exact ⟨a,b,by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),
        by rw [e]; simp (config := {decide := true})⟩)) ?_
  -- memcpy(out, h + 12, 20)
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := SH) (Rv := fun _ => True)
    (fun L => L.lookup (ofString "dst") = some (.val (.word O)) ∧
      (∃ Sr : BitVec 64, L.lookup (ofString "src") = some (.val (.word Sr))) ∧
      L.lookup (ofString "n") = some (.val (.word 20#64))) _ _ _ _ _ originalRuntimeCode_memcpy_lookup
    (memcpyGP O 20#64 (by decide) oO _)
    (fun s values callee rs ⟨⟨⟨_,_,ho⟩,_⟩,hh⟩ args lookup => by
      obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,ho] at ev1; subst ev1
      simp [EV,evalHOLExact,evalListHOLExact,hh,wordOpHOL,wordOp,valueIsWord,valueWord] at ev2; subst ev2
      simp [EV,evalHOLExact] at ev3; subst ev3
      have e := callee_eq originalRuntimeCode_memcpy_lookup lookup
      exact ⟨by rw [e]; simp (config := {decide := true}),⟨H1 + 12#64,by rw [e]; simp (config := {decide := true})⟩,
        by rw [e]; simp (config := {decide := true})⟩)) ?_
  refine aqgd_seq (relMark (LP := SH) Lo Sc H hP0 hcapH hal (fun L h => h.1.2) (fun G h => h.2)) ?_
  exact aqgd_return _ (fun _ _ _ _ _ ⟨_,hH,hs⟩ _ _ => ⟨⟨H,hH,hLoH⟩,hs⟩)

#print axioms ccaTail_wn

/-- The cursor part of `compute_contract_address`: the two fenced field writers at `p`, the list header length and
the list header at `buf + 9 - hl`, then the tail. -/
theorem ccaMid_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O H H1 : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 20 w) (hP0 : P0.toNat ≤ H.toNat)
    (hal : H.toNat % 8 = 0) (hLoH : Lo.toNat ≤ H.toNat) (h64 : H.toNat + 64 ≤ H1.toNat)
    (hcap1 : H1.toNat ≤ 33806089496) (hLo8 : Lo.toNat % 8 = 0) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (((CAL O L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
        L.lookup (ofString "buf") = some (.val (.word H)) ∧ L.lookup (ofString "p") = some (.val (.word (H + 9#64)))) ∧
        HeapIs G H1) ∧ RG Lo Sc G)
      (fun _ _ _ => False) (fun _ _ G => RG Lo Sc G)
      (.decCall (ofString "w") .one (ofString "rlp_encode_bytes") [(.var .local (ofString "p")),(.var .local (ofString "addr")),(.const 20)] (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word") [(.var .local (ofString "p")),(.var .local (ofString "nonce"))]) (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.dec (ofString "payload") .one (.op .sub [(.var .local (ofString "p")),(.op .add [(.var .local (ofString "buf")),(.const 9)])]) (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [(.var .local (ofString "payload"))] (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header") [(.op .sub [(.op .add [(.var .local (ofString "buf")),(.const 9)]),(.var .local (ofString "hl"))]),(.var .local (ofString "payload"))]) (.decCall (ofString "h") .one (ofString "alloc") [(.const 32)] (.seq (.call (some (none,none)) (ofString "keccak256") [(.op .sub [(.op .add [(.var .local (ofString "buf")),(.const 9)]),(.var .local (ofString "hl"))]),(.op .add [(.var .local (ofString "payload")),(.var .local (ofString "hl"))]),(.var .local (ofString "h"))]) (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "out")),(.op .add [(.var .local (ofString "h")),(.const 12)]),(.const 20)]) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.const 0))))))))))))) := by
  have hDF' : DF ≤ 2 ^ 62 := by omega
  have e9 : (H + 9#64).toNat = H.toNat + 9 := by simp [BitVec.toNat_add]; omega
  let GI := fun G : GA => HeapIs G H1 ∧ RG Lo Sc G
  let CM := fun L : GA => (CAL O L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
    L.lookup (ofString "buf") = some (.val (.word H))
  have cmu : ∀ (x : MlS), ofString "addr" ≠ x → ofString "nonce" ≠ x → ofString "out" ≠ x → ofString "mark" ≠ x →
      ofString "buf" ≠ x → ∀ L v, CM L → CM (L.update (x,v)) := fun x h1 h2 h3 h4 h5 L v h =>
    ⟨⟨cal_upd _ h1 h2 h3 _ _ h.1.1,by rw [lookup_update_ne' _ _ h4]; exact h.1.2⟩,
      by rw [lookup_update_ne' _ _ h5]; exact h.2⟩
  refine aqgd_conseq (P := fun L _ G => (CM L ∧ L.lookup (ofString "p") = some (.val (.word (H + 9#64)))) ∧ GI G) ?_
    (fun _ _ _ ⟨⟨⟨⟨a,b⟩,c,d⟩,g⟩,r⟩ => ⟨⟨⟨⟨a,b⟩,c⟩,d⟩,g,r⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  -- w = rlp_encode_bytes(p, addr, 20)
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word (H + 9#64))) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y))) ∧ GI G)
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (G : GA) => WRet DF (H + 9#64) r ∧ GI G)
    (Pc := fun L _ G => (CM L ∧ ∃ P2 : BitVec 64, L.lookup (ofString "p") = some (.val (.word P2)) ∧
      ∃ R1 : BitVec 64, L.lookup (ofString "w") = some (.val (.word R1)) ∧ H.toNat + 9 ≤ P2.toNat ∧
        P2.toNat + R1.toNat ≤ DF + 8) ∧ GI G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup
    (fun _ _ _ _ => cs_bytes (GI := GI) hF hDF' Lo hLo8 hw (H + 9#64) (by omega) (by omega)) ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ G' hG ⟨⟨_,hp⟩,g⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,hp] at ev1; subst ev1
    simp [EV,evalHOLExact] at ev3; subst ev3
    have e := callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),20#64,by rw [e]; simp (config := {decide := true})⟩,g⟩
  · intro L M G v M' G' ⟨⟨cm,hp⟩,_⟩ ⟨⟨R1,hr,hb⟩,g⟩ _
    subst hr
    exact ⟨⟨cmu _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ cm,H + 9#64,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hp,R1,lookup_update_eq' _ _ _,by omega,hb⟩,g⟩
  -- p = p + w
  let CP := fun L : GA => CM L ∧ ∃ P3 : BitVec 64, L.lookup (ofString "p") = some (.val (.word P3)) ∧
    H.toNat + 9 ≤ P3.toNat ∧ P3.toNat ≤ DF + 8
  have asgP : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (CM L ∧ ∃ P2 : BitVec 64, L.lookup (ofString "p") = some (.val (.word P2)) ∧
        ∃ R1 : BitVec 64, L.lookup (ofString "w") = some (.val (.word R1)) ∧ H.toNat + 9 ≤ P2.toNat ∧
          P2.toNat + R1.toNat ≤ DF + 8) ∧ GI G)
      (fun L _ G => CP L ∧ GI G) (fun _ _ G => RG Lo Sc G)
      (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) :=
    aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨cm,P2,hp,R1,hr,lo,hb⟩,g⟩ _ ev => by
      simp [EV,evalHOLExact,evalListHOLExact,hp,hr,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      have e : (P2 + R1).toNat = P2.toNat + R1.toNat := by simp [BitVec.toNat_add]; omega
      exact ⟨⟨cmu _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ cm,P2 + R1,
        lookup_update_eq' _ _ _,by omega,by omega⟩,g⟩)
  refine aqgd_seq asgP ?_
  -- w = rlp_encode_word(p, nonce)
  refine aqgd_seq (aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word (wordOf L0 (ofString "p")))) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "w") = some (.val (.word Y))) ∧ GI G)
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (G : GA) =>
      WRet DF (wordOf L0 (ofString "p")) r ∧ GI G)
    (Q := fun L _ G => (CM L ∧ ∃ P2 : BitVec 64, L.lookup (ofString "p") = some (.val (.word P2)) ∧
        ∃ R1 : BitVec 64, L.lookup (ofString "w") = some (.val (.word R1)) ∧ H.toNat + 9 ≤ P2.toNat ∧
          P2.toNat + R1.toNat ≤ DF + 8) ∧ GI G)
    _ _ _ _ _ _ originalRuntimeCode_rlpEncodeWord_lookup (fun _ _ _ _ _ h => h.elim) (fun h => h) ?_ ?_ ?_) ?_
  · intro L0 _ _ ⟨⟨_,P3,hp,lo,hi⟩,_⟩
    rw [wordOf_eq hp]
    exact cs_word (GI := GI) hF hDF' Lo hLo8 hw P3 (by omega) hi
  · intro F s values callee rs _ G' hG ⟨⟨⟨⟨⟨_,⟨Nc,hn⟩,_⟩,_⟩,_⟩,P3,hp,_⟩,g⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,hp] at ev1; subst ev1
    simp [EV,evalHOLExact,hn] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_rlpEncodeWord_lookup lookup
    rw [wordOf_eq hp]
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),Nc,by rw [e]; simp (config := {decide := true})⟩,g⟩
  · intro L _ _ v _ _ ⟨⟨cm,P3,hp,lo,_⟩,_⟩ ⟨⟨R2,hr,hb⟩,g⟩
    subst hr
    rw [wordOf_eq hp] at hb
    exact ⟨⟨cmu _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ cm,P3,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hp,R2,lookup_update_eq' _ _ _,lo,hb⟩,g⟩
  refine aqgd_seq asgP ?_
  -- payload = p - (buf + 9)
  let CL := fun L : GA => CP L ∧ ∃ PL : BitVec 64, L.lookup (ofString "payload") = some (.val (.word PL))
  refine aqgd_dec (Pb := fun L _ G => CL L ∧ GI G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ ⟨⟨cm,P3,hp,lo,hi⟩,g⟩ _ ev _ => ?_) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · obtain ⟨y,rfl⟩ := ev_op_word s _ _ v ev
    exact ⟨⟨⟨cmu _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ cm,P3,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hp,lo,hi⟩,y,lookup_update_eq' _ _ _⟩,g⟩
  -- hl = rlp_list_header_len(payload)
  let CH := fun L : GA => CM L ∧ ∃ HL : BitVec 64, L.lookup (ofString "hl") = some (.val (.word HL)) ∧ HL.toNat ≤ 9
  refine aqgd_decCallSpecF
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (G : GA) =>
      L.lookup (ofString "payload_len") = some (.val (.word (wordOf L0 (ofString "payload")))) ∧ GI G)
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (G : GA) =>
      (∃ R : BitVec 64, r = .val (.word R) ∧ R.toNat ≤ 9) ∧ GI G)
    (Pc := fun L _ G => CH L ∧ GI G) (Qc := fun _ _ _ => False) _ _ _ _ _ _ _
    originalRuntimeCode_rlpListHeaderLen_lookup
    (fun L0 _ _ _ => aqgd_conseq (aqgd_keepGI (GI := GI)
      (keepsGA_of_installed originalRuntimeCode_rlpListHeaderLen_lookup (by decide))
      (listHeaderLen_spec (wordOf L0 (ofString "payload")))) (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim)
      (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ G' hG ⟨⟨_,PL,hpl⟩,g⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    have := evalList_nil' s _ r1; subst this
    simp [EV,evalHOLExact,hpl] at ev1; subst ev1
    have e := callee_eq originalRuntimeCode_rlpListHeaderLen_lookup lookup
    rw [wordOf_eq hpl]
    exact ⟨by rw [e]; simp (config := {decide := true}),g⟩
  · intro L M G v M' G' ⟨⟨⟨cm,_⟩,_⟩,_⟩ ⟨⟨R,hr,h9⟩,g⟩ _
    subst hr
    exact ⟨⟨cmu _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ cm,R,lookup_update_eq' _ _ _,h9⟩,g⟩
  -- rlp_encode_list_header(buf + 9 - hl, payload)
  refine aqgd_seq (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word (H + 9#64 - wordOf L0 (ofString "hl")))) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "payload_len") = some (.val (.word Y))) ∧ GI G)
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (_ : ValueHOL 64) (_ : Mem) (G : GA) => GI G)
    (Q := fun L _ G => CH L ∧ GI G) _ _ _ _ _ originalRuntimeCode_rlpEncodeListHeader_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 _ _ ⟨⟨_,HL,hh,h9⟩,_⟩
    rw [wordOf_eq hh]
    have e : (H + 9#64 - HL).toNat = H.toNat + 9 - HL.toNat := by
      simp [BitVec.toNat_add,BitVec.toNat_sub]; omega
    exact aqgd_conseq (cs_lh (GI := GI) hF hDF' Lo hLo8 hw (H + 9#64 - HL) (by omega) (by omega))
      (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.2)
  · intro F s values callee rs _ G' hG ⟨⟨⟨_,hb⟩,HL,hh,_⟩,g⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,evalListHOLExact,hb,hh,wordOpHOL,wordOp,valueIsWord,valueWord] at ev1; subst ev1
    obtain ⟨_,y,_,rfl⟩ := entry2_words originalRuntimeCode_rlpEncodeListHeader_lookup lookup
    have e := callee_eq originalRuntimeCode_rlpEncodeListHeader_lookup lookup
    rw [wordOf_eq hh]
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),y,by rw [e]; simp (config := {decide := true})⟩,g⟩
  · intro L _ _ _ _ _ ⟨ch,_⟩ g
    exact ⟨ch,g⟩
  exact aqgd_conseq (ccaTail_wn Lo Sc K Pd O H H1 hK0 hPd0 hw oK oP oO hP0 (by omega) hal hLoH (by omega) hLo8)
    (fun _ _ _ ⟨⟨cm,_⟩,hH,rg⟩ => ⟨⟨cm.1,hH⟩,rg⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ccaMid_wn

/-- The actual `compute_contract_address(addr, nonce, out)` (watched form). -/
theorem cca_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 20 w) (hLo8 : Lo.toNat % 8 = 0) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => CAL O L ∧ RG Lo Sc G) (fun _ _ _ => False) (fun _ _ G => RG Lo Sc G)
      (sourceFunctionBody Guest.guestFn_compute_contract_address) := by
  rw [ccaBody_eq]; unfold ccaBody
  refine aqgd_conseq (P := fun L _ G => ∃ H : BitVec 64, ((CAL O L ∧ HeapIs G H) ∧ ScrIs Sc G) ∧ Lo.toNat ≤ H.toNat)
    (Q := fun _ _ _ => False) ?_ (fun _ _ _ ⟨ls,⟨H,hH,le⟩,hs⟩ => ⟨H,⟨⟨ls,hH⟩,hs⟩,le⟩) (fun _ _ _ h => h)
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
    (Pc := fun L _ G => ((CAL O L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧ HeapIs G H) ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_heap_mark_lookup
    (fun _ M0' G0' ⟨⟨_,hH⟩,_⟩ => heapMark_spec M0' G0' H hH) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨ls,hH⟩,hs⟩ ⟨ev,_,hG⟩ _
    subst ev hG
    exact ⟨⟨⟨cal_upd _ (by decide) (by decide) (by decide) _ _ ls,lookup_update_eq' _ _ _⟩,hH⟩,hs⟩
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 64#64)) ∧ M = M0' ∧ HeapIs G H) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + (64#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => ∃ H1 : BitVec 64, ((((CAL O L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
      L.lookup (ofString "buf") = some (.val (.word H))) ∧ HeapIs G H1) ∧ RG Lo Sc G) ∧
      (H.toNat + 64 ≤ H1.toNat ∧ H1.toNat ≤ 33806089496))
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) 64#64 H M0' G0') ?_ (fun h => h.elim) ?_ ?_
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
  · intro L M G v M' G' ⟨⟨⟨cl,hm⟩,_⟩,hs⟩ ⟨⟨ev,_,H',hH',c1,c2⟩,oh⟩ _
    subst ev
    have : (64#64).toNat = 64 := rfl
    exact ⟨H',⟨⟨⟨⟨cal_upd _ (by decide) (by decide) (by decide) _ _ cl,by rw [lookup_update_ne' _ _ (by decide)]; exact hm⟩,
      lookup_update_eq' _ _ _⟩,hH'⟩,⟨H',hH',by omega⟩,scrIs_onlyHeap oh hs⟩,by omega,c2⟩
  refine aqgd_exE (fun H1 => aqgd_pureE (fun ⟨h64,hcap1⟩ => ?_))
  -- p = buf + 9
  refine aqgd_dec (Pb := fun L _ G => (((CAL O L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
      L.lookup (ofString "buf") = some (.val (.word H)) ∧ L.lookup (ofString "p") = some (.val (.word (H + 9#64)))) ∧
      HeapIs G H1) ∧ RG Lo Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ ⟨⟨⟨⟨cl,hm⟩,hb⟩,hH⟩,rg⟩ _ ev _ => ?_)
    (ccaMid_wn hF hDF hcap Lo Sc K Pd O H H1 hK0 hPd0 hw oK oP oO hP0 hal hLoH h64 hcap1 hLo8)
    (fun _ _ _ _ _ _ _ h => h.elim)
  simp [EV,evalHOLExact,evalListHOLExact,hb,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
  subst ev
  exact ⟨⟨⟨⟨cal_upd _ (by decide) (by decide) (by decide) _ _ cl,by rw [lookup_update_ne' _ _ (by decide)]; exact hm⟩,
    by rw [lookup_update_ne' _ _ (by decide)]; exact hb,lookup_update_eq' _ _ _⟩,hH⟩,rg⟩

#print axioms cca_wn
end cw
end InitECandidate.Runtime
