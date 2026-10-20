import InitECandidate.Runtime.EncAdaptGD
/-!
Cursor-state rules (locals-only cursor `p ∈ [Dst, DF + 8]`, split writer-call / advance steps) and the fenced window
spec of the actual `tx_put_access_list`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem ev_panop_word {F : Type} (s : PanSemStateFiniteExact 64 F) (o : PanOp) (es : List (ExpHOL 64)) (x : ValueHOL 64)
    (h : EV s (.panop o es) = some x) : ∃ y : BitVec 64, x = .val (.word y) := by
  simp only [EV,evalHOLExact] at h
  split at h
  · split at h
    · obtain ⟨y,_,rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨y,rfl⟩
    · cases h
  · cases h

section cd
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {DF : Nat}

theorem cil_dec {base base' : GA → Prop} (Dst : BitVec 64) (name : MlS) (init : ExpHOL 64) {body : ProgHOL 64}
    (hbu : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, base s.locals → EV s init = some v →
      base' (s.locals.update (name,v)))
    (hbr : ∀ L L' : GA, base L → base' L' → base (L'.resVarEq (name,L.lookup name)))
    (hp : ofString "p" ≠ name)
    (hb : AQGD D B A w (fun _ => False) (fun L _ _ => CIL DF base' Dst L) (fun L _ _ => CIL DF base' Dst L) RR body) :
    AQGD D B A w (fun _ => False) (fun L _ _ => CIL DF base Dst L) (fun L _ _ => CIL DF base Dst L) RR
      (.dec name .one init body) :=
  r_dec _ _ _ (fun h => h.elim)
    (fun s v _ ⟨b,P,hP,h1,h2⟩ ev => ⟨hbu s v b ev,P,by rw [lookup_update_ne' _ _ hp]; exact hP,h1,h2⟩) hb
    (fun L L' ⟨b,_⟩ ⟨b',P,hP,h1,h2⟩ => ⟨hbr L L' b b',P,by rw [resVarEq_lookup_ne' _ _ _ _ hp]; exact hP,h1,h2⟩)

theorem cil_decCall_mf {base : GA → Prop} (Dst : BitVec 64) (name function : MlS) (arguments : List (ExpHOL 64))
    {cont : ProgHOL 64} (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (hbu : ∀ L v, base L → base (L.update (name,v))) (hbr : ∀ L L' : GA, base L → base L' → base (L'.resVarEq (name,L.lookup name)))
    (hp : ofString "p" ≠ name)
    (hb : AQGD D B A w (fun _ => False) (fun L _ _ => CIL DF base Dst L) (fun L _ _ => CIL DF base Dst L) RR cont) :
    AQGD D B A w (fun _ => False) (fun L _ _ => CIL DF base Dst L) (fun L _ _ => CIL DF base Dst L) RR
      (.decCall name .one function arguments cont) :=
  r_decCall _ _ _ _ _ _ _ installed mf nb nc (fun h => h.elim)
    (fun L v ⟨b,P,hP,h1,h2⟩ _ => ⟨hbu L v b,P,by rw [lookup_update_ne' _ _ hp]; exact hP,h1,h2⟩) hb
    (fun L L' ⟨b,_⟩ ⟨b',P,hP,h1,h2⟩ => ⟨hbr L L' b b',P,by rw [resVarEq_lookup_ne' _ _ _ _ hp]; exact hP,h1,h2⟩)

theorem cil_assign {base : GA → Prop} (Dst : BitVec 64) (x : MlS) (e : ExpHOL 64)
    (hbu : ∀ L v, base L → base (L.update (x,v))) (hp : ofString "p" ≠ x) :
    AQGD D B A w (fun _ => False) (fun L _ _ => CIL DF base Dst L) (fun L _ _ => CIL DF base Dst L) RR
      (.assign .local x e) :=
  r_assign _ _ (fun s v _ ⟨b,P,hP,h1,h2⟩ _ => ⟨hbu _ v b,P,by rw [lookup_update_ne' _ _ hp]; exact hP,h1,h2⟩)

theorem cil_while {base : GA → Prop} (Dst : BitVec 64) (c : ExpHOL 64) {body : ProgHOL 64}
    (hb : AQGD D B A w (fun _ => False) (fun L _ _ => CIL DF base Dst L) (fun L _ _ => CIL DF base Dst L) RR body) :
    AQGD D B A w (fun _ => False) (fun L _ _ => CIL DF base Dst L) (fun L _ _ => CIL DF base Dst L) RR (.while c body) :=
  r_while (LC := fun _ => True) _ (fun _ _ _ _ _ _ => trivial)
    (aqgd_conseq hb (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))

#print axioms cil_dec
end cd
/-- Cursor state right after a writer call: `w` holds its count, `p + w ≤ DF + 8`. -/
def CILW (DF : Nat) (base : GA → Prop) (Dst : BitVec 64) (L : GA) : Prop :=
  base L ∧ ∃ P R : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧
    L.lookup (ofString "w") = some (.val (.word R)) ∧ Dst.toNat ≤ P.toNat ∧ P.toNat + R.toNat ≤ DF + 8

section cs2
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {DF : Nat}

theorem cs_callL {base : GA → Prop} (Dst : BitVec 64) (hbw : ∀ L v, base L → base (L.update (ofString "w",v)))
    (function : MlS) (arguments : List (ExpHOL 64)) (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (rs : ShapeHOL) (installed : originalRuntimeCode.lookup function = some (parameters,body,rs))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (Pe' : BitVec 64 → GA → Prop)
    (hspec : ∀ P : BitVec 64, Dst.toNat ≤ P.toNat → P.toNat ≤ DF + 8 →
      AQGD D B A w (fun _ => False) (fun L _ G => Pe' P L ∧ (fun _ => True) G) (fun _ _ _ => True)
        (fun r _ G => WRet DF P r ∧ (fun _ => True) G) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs' (P : BitVec 64), base s.locals →
      s.locals.lookup (ofString "p") = some (.val (.word P)) →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs') → Pe' P callee) :
    AQGD D B A w (fun _ => False) (fun L _ _ => CIL DF base Dst L) (fun L _ _ => CILW DF base Dst L) RR
      (.call (some (some (.local,ofString "w"),none)) function arguments) :=
  aqgd_callAssignF (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (G : GA) => Pe' (wordOf L0 (ofString "p")) L ∧ (fun _ => True) G)
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (G' : GA) =>
      WRet DF (wordOf L0 (ofString "p")) r ∧ (fun _ => True) G')
    _ _ _ _ _ _ installed allOne (fun h => h)
    (fun L0 _ _ ⟨_,P,hp,h1,h2⟩ => by rw [wordOf_eq hp]; exact hspec P h1 h2)
    (fun s values callee rs' _ _ _ ⟨hb,P,hp,_⟩ _ args lookup => by
      rw [wordOf_eq hp]; exact ⟨hpe s values callee rs' P hb hp args lookup,trivial⟩)
    (fun L _ _ v _ _ ⟨hb,P,hp,h1,_⟩ ⟨⟨R,hr,hR⟩,_⟩ => by
      rw [wordOf_eq hp] at hR
      subst hr
      exact ⟨hbw _ _ hb,P,R,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,lookup_update_eq' _ _ _,h1,hR⟩)

theorem cs_advL (hDF : DF ≤ 2 ^ 62) {base : GA → Prop} (Dst : BitVec 64)
    (hbp : ∀ L v, base L → base (L.update (ofString "p",v))) :
    AQGD D B A w (fun _ => False) (fun L _ _ => CILW DF base Dst L) (fun L _ _ => CIL DF base Dst L) RR
      (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"),.var .local (ofString "w")])) :=
  r_assign _ _ (fun s v _ ⟨hb,P,R,hp,hr,h1,h2⟩ ev => by
    simp [EV,evalHOLExact,evalListHOLExact,hp,hr,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (P + R).toNat = P.toNat + R.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨hbp _ _ hb,_,lookup_update_eq' _ _ _,by omega,by omega⟩)

#print axioms cs_callL
#print axioms cs_advL
end cs2
section al
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}

/-- The actual `tx_put_access_list(dst, recs, n)`: writes only at or above `dst`, returns `R` with
`dst + R ≤ DF + 8`. -/
theorem putAccessList_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dst : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hD8 : Dst.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)))
      (fun _ _ _ => False) (fun r _ _ => WRet DF Dst r) (sourceFunctionBody Guest.guestFn_tx_put_access_list) := by
  rw [alBody_eq]; unfold alBody
  let AB := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst))
  have abu : ∀ (n : MlS), ofString "dst" ≠ n → ∀ L v, AB L → AB (L.update (n,v)) :=
    fun n hn L v h => by show _ = _; rw [lookup_update_ne' _ _ hn]; exact h
  have abr : ∀ (n : MlS), ofString "dst" ≠ n → ∀ L (o : Option (ValueHOL 64)), AB L → AB (L.resVarEq (n,o)) :=
    fun n hn L o h => by show _ = _; rw [resVarEq_lookup_ne' _ _ _ _ hn]; exact h
  -- pl = access_list_payload_len(recs, n)
  refine r_decCall (LB := fun L => AB L ∧ ∃ PL : BitVec 64, L.lookup (ofString "pl") = some (.val (.word PL)))
    (LQ' := fun _ => False) _ _ _ _ _ _ _ originalRuntimeCode_accessListPayloadLen_lookup
    (memoryFrame_of_good originalRuntimeCode_accessListPayloadLen_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_access_list_payload_len) (by body_check Guest.guestFn_access_list_payload_len)
    (fun h => h.elim) (fun L v h ok => by
      obtain ⟨y,rfl⟩ := scalar_of_shape' ok
      exact ⟨abu _ (by decide) L _ h,y,lookup_update_eq' _ _ _⟩) ?_ (fun _ _ _ h => h)
  -- w = rlp_encode_list_header(dst, pl)
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "payload_len") = some (.val (.word (wordOf L0 (ofString "pl")))))
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => HdrRet DF Dst r)
    (Pc := fun L _ _ => AB L ∧ ∃ W : BitVec 64, L.lookup (ofString "w") = some (.val (.word W)) ∧
      Dst.toNat + W.toNat ≤ DF + 8) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_rlpEncodeListHeader_lookup (by simp)
    (fun L0 _ _ _ => aqgd_conseq (listHeader_win hF Lo hLo8 hw Dst _ hDst (by omega)) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ _ ⟨hd,PL,hpl⟩ _ args lookup
    have hd : s.locals.lookup (ofString "dst") = some (.val (.word Dst)) := hd
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,hpl] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpEncodeListHeader_lookup lookup
    rw [wordOf_eq hpl]
    refine ⟨?_,?_⟩ <;> (rw [e]; simp (config := {decide := true}))
  · intro L _ _ r _ _ ⟨hd,_⟩ ⟨W,hr,_,_,hW⟩ _
    subst hr
    exact ⟨abu _ (by decide) L _ hd,W,lookup_update_eq' _ _ _,hW⟩
  -- p = dst + w; i = 0
  refine r_dec (LB := CIL DF AB Dst) (LQ' := fun _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ ⟨hd,W,hW,hb⟩ ev
    have hd : s.locals.lookup (ofString "dst") = some (.val (.word Dst)) := hd
    simp [EV,evalHOLExact,evalListHOLExact,hd,hW,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (Dst + W).toNat = Dst.toNat + W.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨abu _ (by decide) _ _ hd,_,lookup_update_eq' _ _ _,by omega,by omega⟩
  refine r_dec (LB := CIL DF AB Dst) (LQ' := fun _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ ⟨hd,P,hp,h1,h2⟩ _
    exact ⟨abu _ (by decide) _ _ hd,P,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,h1,h2⟩
  refine aqgd_seq (cil_while Dst _ ?_) (aqgd_return _ ?_)
  · let AB' := fun L : GA => AB L ∧ ∃ y : BitVec 64, L.lookup (ofString "inner") = some (.val (.word y))
    have abu' : ∀ (n : MlS), ofString "dst" ≠ n → ofString "inner" ≠ n → ∀ L v, AB' L → AB' (L.update (n,v)) :=
      fun n h1 h2 L v ⟨h,y,hy⟩ => ⟨abu n h1 L v h,y,by rw [lookup_update_ne' _ _ h2]; exact hy⟩
    have abr' : ∀ (n : MlS), ofString "dst" ≠ n → ofString "inner" ≠ n → ∀ L (o : Option (ValueHOL 64)), AB' L →
        AB' (L.resVarEq (n,o)) :=
      fun n h1 h2 L o ⟨h,y,hy⟩ => ⟨abr n h1 L o h,y,by rw [resVarEq_lookup_ne' _ _ _ _ h2]; exact hy⟩
    refine cil_dec Dst _ _ (fun s v b _ => abu _ (by decide) _ _ b) (fun L L' _ b => abr _ (by decide) _ _ b)
      (by decide) ?_
    refine cil_dec Dst _ _ (fun s v b _ => abu _ (by decide) _ _ b) (fun L L' _ b => abr _ (by decide) _ _ b)
      (by decide) ?_
    refine cil_dec (base' := AB') Dst _ _ (fun s v b ev => by
        obtain ⟨y,rfl⟩ := ev_panop_word s _ _ _ ev
        exact ⟨abu _ (by decide) _ _ b,y,lookup_update_eq' _ _ _⟩)
      (fun L L' _ b => abr _ (by decide) _ _ b.1) (by decide) ?_
    refine cil_decCall_mf Dst _ _ _ _ _ _ originalRuntimeCode_rlpListHeaderLen_lookup
      (memoryFrame_of_good originalRuntimeCode_rlpListHeaderLen_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_rlp_list_header_len) (by body_check Guest.guestFn_rlp_list_header_len)
      (fun L v b => abu' _ (by decide) (by decide) L v b) (fun L L' _ b => abr' _ (by decide) (by decide) _ _ b)
      (by decide) ?_
    have bw := fun L v b => abu' (ofString "w") (by decide) (by decide) L v b
    have bp := fun L v b => abu' (ofString "p") (by decide) (by decide) L v b
    -- rlp_encode_list_header(p, 21 + ih + inner)
    refine aqgd_seq (cs_callL Dst bw _ _ _ _ _ originalRuntimeCode_rlpEncodeListHeader_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "payload_len") = some (.val (.word Y)))
      (fun P h1 h2 => cs_lh hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe2 originalRuntimeCode_rlpEncodeListHeader_lookup (by decide)
        s _ P hp (fun v ev => ev_op_word s _ _ v ev) args lookup)) (aqgd_seq (cs_advL hDF Dst bp) ?_)
    -- rlp_encode_bytes(p, ld (rec + 0), 20)
    refine aqgd_seq (cs_callL Dst bw _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y)))
      (fun P h1 h2 => cs_bytes hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe3 s _ _ P hp
        (fun v ev => by simp [EV,evalHOLExact] at ev; exact ⟨_,ev.symm⟩) args lookup)) (aqgd_seq (cs_advL hDF Dst bp) ?_)
    -- rlp_encode_list_header(p, inner)
    refine aqgd_seq (cs_callL Dst bw _ _ _ _ _ originalRuntimeCode_rlpEncodeListHeader_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "payload_len") = some (.val (.word Y)))
      (fun P h1 h2 => cs_lh hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P b hp args lookup => hpe2 originalRuntimeCode_rlpEncodeListHeader_lookup (by decide)
        s _ P hp (fun v ev => by
          obtain ⟨_,y,hy⟩ := b
          simp [EV,evalHOLExact,hy] at ev; exact ⟨y,ev.symm⟩) args lookup)) (aqgd_seq (cs_advL hDF Dst bp) ?_)
    -- keys, j, inner loop, i += 1
    refine cil_dec (base' := AB') Dst _ _ (fun s v b _ => abu' _ (by decide) (by decide) _ _ b)
      (fun L L' _ b => abr' _ (by decide) (by decide) _ _ b) (by decide) ?_
    refine cil_dec (base' := AB') Dst _ _ (fun s v b _ => abu' _ (by decide) (by decide) _ _ b)
      (fun L L' _ b => abr' _ (by decide) (by decide) _ _ b) (by decide) ?_
    refine aqgd_seq (cil_while Dst _ ?_) (cil_assign Dst _ _ (fun L v b => abu' _ (by decide) (by decide) L v b) (by decide))
    refine aqgd_seq (cs_callL Dst bw _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y)))
      (fun P h1 h2 => cs_bytes hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe3 s _ _ P hp
        (fun v ev => by simp [EV,evalHOLExact] at ev; exact ⟨_,ev.symm⟩) args lookup))
      (aqgd_seq (cs_advL hDF Dst bp) (cil_assign Dst _ _ (fun L v b => abu' _ (by decide) (by decide) L v b) (by decide)))
  · intro F s v _ _ _ ⟨hd,P,hp,h1,h2⟩ _ ev
    have hd : s.locals.lookup (ofString "dst") = some (.val (.word Dst)) := hd
    simp [EV,evalHOLExact,evalListHOLExact,hp,hd,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (P - Dst).toNat = P.toNat - Dst.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    exact ⟨P - Dst,rfl,by rw [e1]; omega⟩

#print axioms putAccessList_win
end al
end InitECandidate.Runtime
