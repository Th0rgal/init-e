import InitECandidate.Runtime.EncCursorGGD
/-!
Fenced window spec of the actual `tx_put_authorizations` (cursor steps through list headers, `tx_put_u256`,
`rlp_encode_bytes`, `rlp_encode_word`), keeping the heap pointer.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section csS
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {DF : Nat} {base GI : GA → Prop}

/-- `csg_call` for writers with struct parameters. -/
theorem csg_callS (Dst : BitVec 64) (hbw : ∀ L v, base L → base (L.update (ofString "w",v)))
    (function : MlS) (arguments : List (ExpHOL 64)) (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (rs : ShapeHOL) (installed : originalRuntimeCode.lookup function = some (parameters,body,rs))
    (Pe' : BitVec 64 → GA → Prop)
    (hspec : ∀ P : BitVec 64, Dst.toNat ≤ P.toNat → P.toNat ≤ DF + 8 →
      AQGD D B A w (fun _ => False) (fun L _ G => Pe' P L ∧ GI G) (fun _ _ _ => True)
        (fun r _ G => WRet DF P r ∧ GI G) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs' (P : BitVec 64), base s.locals →
      s.locals.lookup (ofString "p") = some (.val (.word P)) →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs') → Pe' P callee) :
    AQGD D B A w (fun _ => False) (fun L _ G => CIG DF base GI Dst L G) (fun L _ G => CIGW DF base GI Dst L G) RR
      (.call (some (some (.local,ofString "w"),none)) function arguments) :=
  aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (G : GA) => Pe' (wordOf L0 (ofString "p")) L ∧ GI G)
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (G' : GA) =>
      WRet DF (wordOf L0 (ofString "p")) r ∧ GI G')
    _ _ _ _ _ _ installed (fun _ _ _ _ _ h => h.elim) (fun h => h)
    (fun L0 _ _ ⟨_,_,P,hp,h1,h2⟩ => by rw [wordOf_eq hp]; exact hspec P h1 h2)
    (fun s values callee rs' _ H hH ⟨hb,hg,P,hp,_⟩ _ args lookup => by
      unfold GIs at hH; subst hH
      rw [wordOf_eq hp]; exact ⟨hpe s values callee rs' P hb hp args lookup,hg⟩)
    (fun L _ _ v _ _ ⟨hb,_,P,hp,h1,_⟩ ⟨⟨R,hr,hR⟩,hg⟩ => by
      rw [wordOf_eq hp] at hR
      subst hr
      exact ⟨hbw _ _ hb,hg,P,R,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,lookup_update_eq' _ _ _,h1,hR⟩)

#print axioms csg_callS
end csS

section au
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {DF : Nat} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- The actual `tx_put_authorizations(dst, recs, n)`: writes only at or above `dst` and in temporary heap blocks at or
above the heap pointer `H` (restored); returns `R` with `dst + R ≤ DF + 8`. -/
theorem putAuthorizations_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (Lo : BitVec 64)
    (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (Dst H : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat)
    (hD8 : Dst.toNat ≤ DF + 8) (hLoH : Lo.toNat ≤ H.toNat) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ HeapIs G H)
      (fun _ _ _ => False) (fun r _ G => WRet DF Dst r ∧ HeapIs G H)
      (sourceFunctionBody Guest.guestFn_tx_put_authorizations) := by
  rw [auBody_eq]; unfold auBody
  let AB := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst))
  let GH := fun G : GA => HeapIs G H
  have abu : ∀ (n : MlS), ofString "dst" ≠ n → ∀ L v, AB L → AB (L.update (n,v)) :=
    fun n hn L v h => by show _ = _; rw [lookup_update_ne' _ _ hn]; exact h
  have abr : ∀ (n : MlS), ofString "dst" ≠ n → ∀ L (o : Option (ValueHOL 64)), AB L → AB (L.resVarEq (n,o)) :=
    fun n hn L o h => by show _ = _; rw [resVarEq_lookup_ne' _ _ _ _ hn]; exact h
  -- total = auth_list_payload_len(recs, n)
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => (AB L ∧ ∃ T : BitVec 64, L.lookup (ofString "total") = some (.val (.word T))) ∧ GH G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_authListPayloadLen_lookup
    (fun _ M0' G0' _ => aqgd_of_mf (memoryFrame_of_good originalRuntimeCode_authListPayloadLen_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_auth_list_payload_len) (by body_check Guest.guestFn_auth_list_payload_len) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro L M G v M' G' ⟨hd,hH⟩ ⟨_,e2⟩ ok
    subst e2
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    exact ⟨⟨abu _ (by decide) L _ hd,y,lookup_update_eq' _ _ _⟩,hH⟩
  -- w = rlp_encode_list_header(dst, total)
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (G0' : GA) (L : GA) (_ : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "payload_len") = some (.val (.word (wordOf L0 (ofString "total"))))) ∧ GH G)
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (G' : GA) => HdrRet DF Dst r ∧ GH G')
    (Pc := fun L _ G => (AB L ∧ ∃ W : BitVec 64, L.lookup (ofString "w") = some (.val (.word W)) ∧
      Dst.toNat + W.toNat ≤ DF + 8) ∧ GH G) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_rlpEncodeListHeader_lookup (by simp)
    (fun L0 _ _ _ => aqgd_conseq (aqgd_keepGI (GI := GH)
      (keepsGA_of_installed originalRuntimeCode_rlpEncodeListHeader_lookup (by decide))
      (listHeader_win hF Lo hLo8 hw Dst _ hDst (by omega))) (fun _ _ _ h => h)
      (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ hG ⟨⟨hd,T,ht⟩,hH⟩ _ args lookup
    have hd : s.locals.lookup (ofString "dst") = some (.val (.word Dst)) := hd
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,ht] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpEncodeListHeader_lookup lookup
    rw [wordOf_eq ht]
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,hH⟩
  · intro L _ _ r _ _ ⟨⟨hd,_⟩,_⟩ ⟨⟨W,hr,_,_,hW⟩,hH⟩ _
    subst hr
    exact ⟨⟨abu _ (by decide) L _ hd,W,lookup_update_eq' _ _ _,hW⟩,hH⟩
  -- p = dst + w; i = 0
  refine aqgd_dec (Pb := fun L _ G => CIG DF AB GH Dst L G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s v _ _ hG ⟨⟨hd,W,hW,hb⟩,hH⟩ _ ev _
    have hd : s.locals.lookup (ofString "dst") = some (.val (.word Dst)) := hd
    unfold GIs at hG; subst hG
    simp [EV,evalHOLExact,evalListHOLExact,hd,hW,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (Dst + W).toNat = Dst.toNat + W.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨abu _ (by decide) _ _ hd,hH,_,lookup_update_eq' _ _ _,by omega,by omega⟩
  refine aqgd_dec (Pb := fun L _ G => CIG DF AB GH Dst L G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v _ _ hG ⟨b,g,P,hP,h1,h2⟩ _ _ _ => by
      unfold GIs at hG; subst hG
      exact ⟨abu _ (by decide) _ _ b,g,P,by rw [lookup_update_ne' _ _ (by decide)]; exact hP,h1,h2⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq (cig_while Dst _ ?_) (aqgd_return _ ?_)
  · let AB' := fun L : GA => AB L ∧ ∃ y : BitVec 64, L.lookup (ofString "pl") = some (.val (.word y))
    have abu' : ∀ (n : MlS), ofString "dst" ≠ n → ofString "pl" ≠ n → ∀ L v, AB' L → AB' (L.update (n,v)) :=
      fun n h1 h2 L v ⟨h,y,hy⟩ => ⟨abu n h1 L v h,y,by rw [lookup_update_ne' _ _ h2]; exact hy⟩
    have bw := fun L v b => abu' (ofString "w") (by decide) (by decide) L v b
    have bp := fun L v b => abu' (ofString "p") (by decide) (by decide) L v b
    refine cig_dec (base' := AB) Dst (ofString "a") _ (fun s v b _ => abu _ (by decide) _ _ b)
      (fun L L' _ b => abr _ (by decide) _ _ b) (by decide) ?_
    refine cig_decCall_mf (base' := AB') Dst (ofString "pl") _ _ _ _ _ originalRuntimeCode_authPayloadLen_lookup
      (memoryFrame_of_good originalRuntimeCode_authPayloadLen_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_auth_payload_len) (by body_check Guest.guestFn_auth_payload_len)
      (fun L v b ok => by
        obtain ⟨y,rfl⟩ := scalar_of_shape' ok
        exact ⟨abu _ (by decide) L _ b,y,lookup_update_eq' _ _ _⟩)
      (fun L L' _ b => abr _ (by decide) _ _ b.1) (by decide) ?_
    refine aqgd_seq (csg_call (base := AB') Dst bw _ _ _ _ _ originalRuntimeCode_rlpEncodeListHeader_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "payload_len") = some (.val (.word Y)))
      (fun P h1 h2 => cs_lh (GI := GH) hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P b hp args lookup => hpe2 originalRuntimeCode_rlpEncodeListHeader_lookup (by decide)
        s _ P hp (fun v ev => by
          obtain ⟨_,y,hy⟩ := b
          simp [EV,evalHOLExact,hy] at ev; exact ⟨y,ev.symm⟩) args lookup))
      (aqgd_seq (csg_adv hDF Dst bp) ?_)
    refine aqgd_seq (csg_callS (base := AB') Dst bw _ _ _ _ _ originalRuntimeCode_txPutU256_lookup
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)))
      (fun P h1 h2 => cs_u256 hF hDF hcap Lo hLo8 hw H hLoH P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpeU s _ P hp args lookup))
      (aqgd_seq (csg_adv hDF Dst bp) ?_)
    refine aqgd_seq (csg_call (base := AB') Dst bw _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y)))
      (fun P h1 h2 => cs_bytes (GI := GH) hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe3 s _ _ P hp
        (fun v ev => by simp [EV,evalHOLExact] at ev; exact ⟨_,ev.symm⟩) args lookup))
      (aqgd_seq (csg_adv hDF Dst bp) ?_)
    refine aqgd_seq (csg_call (base := AB') Dst bw _ _ _ _ _ originalRuntimeCode_rlpEncodeWord_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "w") = some (.val (.word Y)))
      (fun P h1 h2 => cs_word (GI := GH) hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe2 originalRuntimeCode_rlpEncodeWord_lookup (by decide)
        s _ P hp (fun v ev => ev_load_one_word s _ v ev) args lookup))
      (aqgd_seq (csg_adv hDF Dst bp) ?_)
    refine aqgd_seq (csg_call (base := AB') Dst bw _ _ _ _ _ originalRuntimeCode_rlpEncodeWord_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "w") = some (.val (.word Y)))
      (fun P h1 h2 => cs_word (GI := GH) hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe2 originalRuntimeCode_rlpEncodeWord_lookup (by decide)
        s _ P hp (fun v ev => ev_load_one_word s _ v ev) args lookup))
      (aqgd_seq (csg_adv hDF Dst bp) ?_)
    refine aqgd_seq (csg_callS (base := AB') Dst bw _ _ _ _ _ originalRuntimeCode_txPutU256_lookup
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)))
      (fun P h1 h2 => cs_u256 hF hDF hcap Lo hLo8 hw H hLoH P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpeU s _ P hp args lookup))
      (aqgd_seq (csg_adv hDF Dst bp) ?_)
    exact aqgd_seq (csg_callS (base := AB') Dst bw _ _ _ _ _ originalRuntimeCode_txPutU256_lookup
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)))
      (fun P h1 h2 => cs_u256 hF hDF hcap Lo hLo8 hw H hLoH P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpeU s _ P hp args lookup))
      (aqgd_seq (csg_adv hDF Dst bp) (cig_assign Dst (ofString "i") _ (fun L v b => abu' _ (by decide) (by decide) L v b) (by decide)))
  · intro F s v _ _ _ ⟨hd,hH,P,hp,h1,h2⟩ _ ev
    have hd : s.locals.lookup (ofString "dst") = some (.val (.word Dst)) := hd
    simp [EV,evalHOLExact,evalListHOLExact,hp,hd,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (P - Dst).toNat = P.toNat - Dst.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    exact ⟨⟨P - Dst,rfl,by rw [e1]; omega⟩,hH⟩
#print axioms putAuthorizations_win
end au
end InitECandidate.Runtime
