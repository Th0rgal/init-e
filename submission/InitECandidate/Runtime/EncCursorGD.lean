import InitECandidate.Runtime.EncPutU256GD
/-!
Fenced window spec of the actual `tx_put_blob_hashes`, and a generic cursor step `w = f(p, …); p = p + w` keeping the
cursor in `[Dst, DF + 8]` against any writer spec that returns within the fence.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def bhBody : ProgHOL 64 :=
  ProgHOL.decCall (ofString "w") ShapeHOL.one (ofString "rlp_encode_list_header") [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.panop PanOp.mul [ExpHOL.const 33#64, ExpHOL.var VarKind.local (ofString "n")]] (ProgHOL.dec (ofString "p") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "w")]) (ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "buf"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 32#64]], ExpHOL.const 32#64]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64]))))) (ProgHOL.return (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "dst")])))))

theorem bhBody_eq : sourceFunctionBody Guest.guestFn_tx_put_blob_hashes = bhBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_tx_put_blob_hashes,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- Loop state of `tx_put_blob_hashes`: parameters, word counters, and the cursor `p ∈ [Dst, DF + 8]`. -/
def BhI (DF : Nat) (Dst Bf Nn : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup (ofString "buf") = some (.val (.word Bf)) ∧
    L.lookup (ofString "n") = some (.val (.word Nn)) ∧
    (∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I))) ∧
    (∃ W : BitVec 64, L.lookup (ofString "w") = some (.val (.word W))) ∧
    ∃ P : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧ Dst.toNat ≤ P.toNat ∧ P.toNat ≤ DF + 8

section bh
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}

/-- The actual `tx_put_blob_hashes(dst, buf, n)`: writes only at or above `dst`; returns `R` with
`dst + R ≤ DF + 8`. -/
theorem putBlobHashes_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dst Bf Nn : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hD8 : Dst.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "buf") = some (.val (.word Bf)) ∧ L.lookup (ofString "n") = some (.val (.word Nn)))
      (fun _ _ _ => False) (fun r _ _ => WRet DF Dst r) (sourceFunctionBody Guest.guestFn_tx_put_blob_hashes) := by
  rw [bhBody_eq]; unfold bhBody
  -- w = rlp_encode_list_header(dst, 33 * n)
  let P1 := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
    L.lookup (ofString "buf") = some (.val (.word Bf)) ∧ L.lookup (ofString "n") = some (.val (.word Nn)) ∧
    ∃ W : BitVec 64, L.lookup (ofString "w") = some (.val (.word W)) ∧ Dst.toNat + W.toNat ≤ DF + 8
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "payload_len") = some (.val (.word (33#64 * Nn))))
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => HdrRet DF Dst r)
    (Pc := fun L _ _ => P1 L) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_rlpEncodeListHeader_lookup (by simp)
    (fun _ _ _ _ => aqgd_conseq (listHeader_win hF Lo hLo8 hw Dst (33#64 * Nn) hDst (by omega)) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ _ ⟨hd,_,hn⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,hn,panOpHOL,valueIsWord,valueWord] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpEncodeListHeader_lookup lookup
    refine ⟨?_,?_⟩ <;> (rw [e]; simp (config := {decide := true}))
  · intro L _ _ r _ _ ⟨hd,hb,hn⟩ ⟨W,hr,_,_,hW⟩ _
    subst hr
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hb,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hn,W,lookup_update_eq' _ _ _,hW⟩
  -- p = dst + w; i = 0
  refine r_dec (LB := fun L => (P1 L ∧ ∃ P : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧
      Dst.toNat ≤ P.toNat ∧ P.toNat ≤ DF + 8)) (LQ' := fun _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ ⟨hd,hb,hn,W,hW,hb8⟩ ev
    simp [EV,evalHOLExact,evalListHOLExact,hd,hW,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (Dst + W).toNat = Dst.toNat + W.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hb,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hn,W,by rw [lookup_update_ne' _ _ (by decide)]; exact hW,hb8⟩,
      _,lookup_update_eq' _ _ _,by omega,by omega⟩
  refine r_dec (LB := BhI DF Dst Bf Nn) (LQ' := fun _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ ⟨⟨hd,hb,hn,W,hW,_⟩,P,hp,h1,h2⟩ ev
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hb,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hn,⟨_,lookup_update_eq' _ _ _⟩,
      ⟨W,by rw [lookup_update_ne' _ _ (by decide)]; exact hW⟩,P,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,h1,h2⟩
  refine aqgd_seq (r_while (LC := fun _ => True) _ (fun _ _ _ _ _ _ => trivial) ?_) (aqgd_return _ ?_)
  · refine aqgd_conseq (P := fun L _ _ => BhI DF Dst Bf Nn L) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
    -- w = rlp_encode_bytes(p, buf + i*32, 32)
    let Q1 := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
      L.lookup (ofString "buf") = some (.val (.word Bf)) ∧ L.lookup (ofString "n") = some (.val (.word Nn)) ∧
      (∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I))) ∧
      ∃ P W : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧
        L.lookup (ofString "w") = some (.val (.word W)) ∧ Dst.toNat ≤ P.toNat ∧ P.toNat + W.toNat ≤ DF + 8
    refine aqgd_seq (aqgd_callAssignF (Vn' := fun _ => False)
      (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
        L.lookup (ofString "dst") = some (.val (.word (wordOf L0 (ofString "p")))) ∧
          L.lookup (ofString "n") = some (.val (.word 32#64)))
      (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => WRet DF (wordOf L0 (ofString "p")) r)
      (Q := fun L _ _ => Q1 L) _ _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup (by simp) (fun h => h)
      ?_ ?_ ?_) (aqgd_seq (r_assign (LQ := BhI DF Dst Bf Nn) _ _ ?_) (r_assign _ _ ?_))
    · intro L0 _ _ ⟨_,_,_,_,_,P,hp,h1,h2⟩
      rw [wordOf_eq hp]
      exact aqgd_conseq (encodeBytes_win hF hDF Lo hLo8 hw P 32#64 (by omega) (by omega)) (fun _ _ _ h => h)
        (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
    · intro F s values callee rs _ _ _ ⟨hd,hb,hn,⟨I,hi⟩,_,P,hp,_⟩ _ args lookup
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hp,hb,hi,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL] at args
      subst args
      have e := callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
      rw [wordOf_eq hp]
      refine ⟨?_,?_⟩ <;> (rw [e]; simp (config := {decide := true}))
    · intro L _ _ v _ _ ⟨hd,hb,hn,hi,_,P,hp,h1,h2⟩ ⟨R,hr,hR⟩
      rw [wordOf_eq hp] at hR
      subst hr
      obtain ⟨I,hi⟩ := hi
      exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hb,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hn,⟨I,by rw [lookup_update_ne' _ _ (by decide)]; exact hi⟩,
        P,R,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,lookup_update_eq' _ _ _,h1,hR⟩
    · intro F s v _ ⟨hd,hb,hn,hi,P,W,hp,hW,h1,h2⟩ ev
      simp [EV,evalHOLExact,evalListHOLExact,hp,hW,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
      have e1 : (P + W).toNat = P.toNat + W.toNat := by simp [BitVec.toNat_add]; omega
      obtain ⟨I,hi⟩ := hi
      exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hb,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hn,⟨I,by rw [lookup_update_ne' _ _ (by decide)]; exact hi⟩,
        ⟨W,by rw [lookup_update_ne' _ _ (by decide)]; exact hW⟩,_,lookup_update_eq' _ _ _,by omega,by omega⟩
    · intro F s v _ ⟨hd,hb,hn,⟨I,hi⟩,hW,P,hp,h1,h2⟩ ev
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
      obtain ⟨W,hW⟩ := hW
      exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hb,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hn,⟨_,lookup_update_eq' _ _ _⟩,
        ⟨W,by rw [lookup_update_ne' _ _ (by decide)]; exact hW⟩,P,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,h1,h2⟩
  · intro F s v _ _ _ ⟨hd,_,_,_,_,P,hp,h1,h2⟩ _ ev
    simp [EV,evalHOLExact,evalListHOLExact,hp,hd,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (P - Dst).toNat = P.toNat - Dst.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    exact ⟨P - Dst,rfl,by rw [e1]; omega⟩

#print axioms putBlobHashes_win
end bh
/-- Cursor state: frame-independent locals `base`, a globals invariant `GI`, and the cursor `p ∈ [Dst, DF + 8]`. -/
def CI (DF : Nat) (base : GA → Prop) (GI : GA → Prop) (Dst : BitVec 64) (L : GA) (G : GA) : Prop :=
  base L ∧ GI G ∧ ∃ P : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧ Dst.toNat ≤ P.toNat ∧
    P.toNat ≤ DF + 8

section cs
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {DF : Nat}

/-- One cursor step `w = f(p, …); p = p + w` against a writer spec returning within the fence. -/
theorem cursor_step (hDF : DF ≤ 2 ^ 62) {base GI : GA → Prop} (Dst : BitVec 64)
    (hbw : ∀ L v, base L → base (L.update (ofString "w",v))) (hbp : ∀ L v, base L → base (L.update (ofString "p",v)))
    (function : MlS) (arguments : List (ExpHOL 64)) (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (rs : ShapeHOL) (installed : originalRuntimeCode.lookup function = some (parameters,body,rs))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (Pe' : BitVec 64 → GA → Prop)
    (hspec : ∀ P : BitVec 64, Dst.toNat ≤ P.toNat → P.toNat ≤ DF + 8 →
      AQGD D B A w (fun _ => False) (fun L _ G => Pe' P L ∧ GI G) (fun _ _ _ => True)
        (fun r _ G => WRet DF P r ∧ GI G) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs' (P : BitVec 64), base s.locals →
      s.locals.lookup (ofString "p") = some (.val (.word P)) →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs') → Pe' P callee) :
    AQGD D B A w (fun _ => False) (fun L _ G => CI DF base GI Dst L G) (fun L _ G => CI DF base GI Dst L G) RR
      (.seq (.call (some (some (.local,ofString "w"),none)) function arguments)
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"),.var .local (ofString "w")]))) := by
  refine aqgd_seq (Q := fun L _ G => base L ∧ GI G ∧ ∃ P R : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧
      L.lookup (ofString "w") = some (.val (.word R)) ∧ Dst.toNat ≤ P.toNat ∧ P.toNat + R.toNat ≤ DF + 8)
    (aqgd_callAssignF (Vn' := fun _ => False)
      (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (G : GA) => Pe' (wordOf L0 (ofString "p")) L ∧ GI G)
      (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (G' : GA) =>
        WRet DF (wordOf L0 (ofString "p")) r ∧ GI G')
      _ _ _ _ _ _ installed allOne (fun h => h) ?_ ?_ ?_) ?_
  · intro L0 _ _ ⟨_,_,P,hp,h1,h2⟩
    rw [wordOf_eq hp]
    exact hspec P h1 h2
  · intro F s values callee rs' _ H hH ⟨hb,hg,P,hp,_⟩ _ args lookup
    unfold GIs at hH; subst hH
    rw [wordOf_eq hp]
    exact ⟨hpe s values callee rs' P hb hp args lookup,hg⟩
  · intro L _ _ v _ G' ⟨hb,_,P,hp,h1,_⟩ ⟨⟨R,hr,hR⟩,hg⟩
    rw [wordOf_eq hp] at hR
    subst hr
    exact ⟨hbw _ _ hb,hg,P,R,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,lookup_update_eq' _ _ _,h1,hR⟩
  · refine aqgd_assignLocal _ _ (fun s v _ _ ⟨hb,hg,P,R,hp,hr,h1,h2⟩ _ ev => ?_)
    simp [EV,evalHOLExact,evalListHOLExact,hp,hr,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (P + R).toNat = P.toNat + R.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨hbp _ _ hb,hg,_,lookup_update_eq' _ _ _,by omega,by omega⟩

#print axioms cursor_step
end cs
end InitECandidate.Runtime
