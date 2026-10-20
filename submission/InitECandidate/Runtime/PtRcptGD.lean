import InitECandidate.Runtime.PtSufAGD
import InitECandidate.Runtime.OriginalPtRcptCode
/-!
Fenced window specs of the receipt encoders: `rlp_finish_list(dst, payload_end)` (header length, the payload moved
down to `dst + hl` by a fenced `memcpy`, the list header at `dst`), returning `R` with `dst + R ≤ DF + 8`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def flBody : ProgHOL 64 :=
  (.dec (ofString "payload") .one (.op .sub [(.var .local (ofString "payload_end")),(.op .add [(.var .local (ofString "dst")),(.const 9)])]) (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [(.var .local (ofString "payload"))] (.seq (.call (some (none,none)) (ofString "memcpy") [(.op .add [(.var .local (ofString "dst")),(.var .local (ofString "hl"))]),(.op .add [(.var .local (ofString "dst")),(.const 9)]),(.var .local (ofString "payload"))]) (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header") [(.var .local (ofString "dst")),(.var .local (ofString "payload"))]) (.return (.op .add [(.var .local (ofString "hl")),(.var .local (ofString "payload"))]))))))

theorem flBody_eq : sourceFunctionBody Guest.guestFn_rlp_finish_list = flBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_finish_list,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


section fl
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}

/-- The actual `rlp_finish_list(dst, payload_end)` with `dst + 9 ≤ payload_end ≤ DF + 8`: writes only at or above
`dst`, returns `R` with `dst + R ≤ DF + 8`. -/
theorem finishList_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dst Pe : BitVec 64) (h1 : Lo.toNat ≤ Dst.toNat) (h2 : Dst.toNat + 9 ≤ Pe.toNat)
    (h3 : Pe.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "payload_end") = some (.val (.word Pe)))
      (fun _ _ _ => False) (fun r _ _ => WRet DF Dst r) (sourceFunctionBody Guest.guestFn_rlp_finish_list) := by
  rw [flBody_eq]; unfold flBody
  have e9 : (Dst + 9#64).toNat = Dst.toNat + 9 := by simp [BitVec.toNat_add]; omega
  have ePL : (Pe - (Dst + 9#64)).toNat = Pe.toNat - (Dst.toNat + 9) := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e9]; omega), e9]
  let L1 := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
    L.lookup (ofString "payload") = some (.val (.word (Pe - (Dst + 9#64))))
  refine aqgd_dec (Pb := fun L _ _ => L1 L) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ ⟨hd,hp⟩ _ ev _ => ?_) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · simp [EV,evalHOLExact,evalListHOLExact,hd,hp,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,lookup_update_eq' _ _ _⟩
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      L.lookup (ofString "payload_len") = some (.val (.word (Pe - (Dst + 9#64)))))
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) =>
      ∃ R : BitVec 64, r = .val (.word R) ∧ R.toNat ≤ 9)
    (Pc := fun L _ _ => L1 L ∧ ∃ HL : BitVec 64, L.lookup (ofString "hl") = some (.val (.word HL)) ∧ HL.toNat ≤ 9)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_rlpListHeaderLen_lookup
    (fun _ _ _ _ => aqgd_conseq (listHeaderLen_spec (Pe - (Dst + 9#64))) (fun _ _ _ h => h) (fun _ _ _ h => h.elim)
      (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ G hG ⟨_,hp⟩ _ args lookup
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    have := evalList_nil' s _ r1; subst this
    simp [EV,evalHOLExact,hp] at ev1; subst ev1
    have e := callee_eq originalRuntimeCode_rlpListHeaderLen_lookup lookup
    rw [e]; simp (config := {decide := true})
  · intro L M G v M' G' ⟨hd,hp⟩ ⟨R,hr,h9⟩ _
    subst hr
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hp⟩,
      R,lookup_update_eq' _ _ _,h9⟩
  -- memcpy(dst + hl, dst + 9, payload)
  refine aqgd_seq (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      L.lookup (ofString "dst") = some (.val (.word (Dst + wordOf L0 (ofString "hl")))) ∧
        L.lookup (ofString "n") = some (.val (.word (Pe - (Dst + 9#64)))))
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (_ : ValueHOL 64) (_ : Mem) (_ : GA) =>
      (Dst + wordOf L0 (ofString "hl")).toNat + (Pe - (Dst + 9#64)).toNat ≤ DF + 8)
    (Q := fun L _ _ => (L1 L ∧ ∃ HL : BitVec 64, L.lookup (ofString "hl") = some (.val (.word HL)) ∧ HL.toNat ≤ 9) ∧
      (Dst + wordOf L (ofString "hl")).toNat + (Pe - (Dst + 9#64)).toNat ≤ DF + 8)
    _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 _ _ ⟨_,HL,hh,h9⟩
    rw [wordOf_eq hh]
    have e : (Dst + HL).toNat = Dst.toNat + HL.toNat := by simp [BitVec.toNat_add]; omega
    exact aqgd_conseq (memcpy_win (Vn := fun _ => False) (A := A) (B := B) hF hDF Lo hLo8 hw (Dst + HL)
      (Pe - (Dst + 9#64)) (by omega) (by omega)) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ G hG ⟨⟨hd,hp⟩,HL,hh,_⟩ _ args lookup
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,evalListHOLExact,hd,hh,wordOpHOL,wordOp,valueIsWord,valueWord] at ev1; subst ev1
    simp [EV,evalHOLExact,hp] at ev3; subst ev3
    have e := callee_eq originalRuntimeCode_memcpy_lookup lookup
    rw [wordOf_eq hh]
    exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩
  · intro L _ _ _ _ _ pre hb
    exact ⟨pre,hb⟩
  -- rlp_encode_list_header(dst, payload)
  refine aqgd_seq (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "payload_len") = some (.val (.word (Pe - (Dst + 9#64)))))
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (_ : ValueHOL 64) (_ : Mem) (_ : GA) => True)
    (Q := fun L _ _ => (L1 L ∧ ∃ HL : BitVec 64, L.lookup (ofString "hl") = some (.val (.word HL)) ∧ HL.toNat ≤ 9) ∧
      (Dst + wordOf L (ofString "hl")).toNat + (Pe - (Dst + 9#64)).toNat ≤ DF + 8)
    _ _ _ _ _ originalRuntimeCode_rlpEncodeListHeader_lookup (by simp)
    (fun _ _ _ _ => aqgd_conseq (listHeader_win (A := A) (B := B) hF Lo hLo8 hw Dst (Pe - (Dst + 9#64)) h1 (by omega))
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ _ => trivial)) ?_ (fun _ _ _ _ _ _ pre _ => pre)) ?_
  · intro F s values callee rs _ G hG ⟨⟨⟨hd,hp⟩,_⟩,_⟩ _ args lookup
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,hd] at ev1; subst ev1
    simp [EV,evalHOLExact,hp] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_rlpEncodeListHeader_lookup lookup
    exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩
  refine aqgd_return _ (fun s v _ _ _ ⟨⟨⟨_,hp⟩,HL,hh,h9⟩,hb⟩ _ ev => ?_)
  simp [EV,evalHOLExact,evalListHOLExact,hh,hp,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
  subst ev
  rw [wordOf_eq hh] at hb
  have e : (Dst + HL).toNat = Dst.toNat + HL.toNat := by simp [BitVec.toNat_add]; omega
  have e2 : (HL + (Pe - (Dst + 9#64))).toNat = HL.toNat + (Pe - (Dst + 9#64)).toNat := by
    simp [BitVec.toNat_add]; omega
  exact ⟨_,rfl,by rw [e2]; omega⟩

#print axioms finishList_win
end fl
def atbBody : ProgHOL 64 :=
  (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "h") .one (ofString "alloc") [(.const 32)] (.seq (.call (some (none,none)) (ofString "keccak256") [(.var .local (ofString "entry")),(.var .local (ofString "n")),(.var .local (ofString "h"))]) (.dec (ofString "idx") .one (.const 0) (.seq (.while (.cmp .less (.var .local (ofString "idx")) (.const 6)) (.dec (ofString "bit") .one (.op .and [(.op .or [(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "h")),(.var .local (ofString "idx"))])) (.const 8)),(.loadByte (.op .add [(.var .local (ofString "h")),(.var .local (ofString "idx")),(.const 1)]))]),(.const 2047)]) (.dec (ofString "bit_index") .one (.op .sub [(.const 2047),(.var .local (ofString "bit"))]) (.dec (ofString "byte_index") .one (.shift .lsr (.var .local (ofString "bit_index")) (.const 3)) (.dec (ofString "bv") .one (.shift .lsl (.const 1) (.op .sub [(.const 7),(.op .and [(.var .local (ofString "bit_index")),(.const 7)])])) (.seq (.storeByte (.op .add [(.var .local (ofString "bloom")),(.var .local (ofString "byte_index"))]) (.op .or [(.loadByte (.op .add [(.var .local (ofString "bloom")),(.var .local (ofString "byte_index"))])),(.var .local (ofString "bv"))])) (.assign .local (ofString "idx") (.op .add [(.var .local (ofString "idx")),(.const 2)])))))))) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.const 0))))))))

theorem atbBody_eq : sourceFunctionBody Guest.guestFn_add_to_bloom = atbBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_add_to_bloom,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


/-- Locals of `add_to_bloom` after `mark` and `h`. -/
def ATB (Bl H H1 : BitVec 64) (L : GA) : Prop :=
  (((L.lookup (ofString "bloom") = some (.val (.word Bl)) ∧
    (∃ E : BitVec 64, L.lookup (ofString "entry") = some (.val (.word E))) ∧
    (∃ N : BitVec 64, L.lookup (ofString "n") = some (.val (.word N)))) ∧
    L.lookup (ofString "mark") = some (.val (.word H))) ∧ L.lookup (ofString "h") = some (.val (.word H1)))

theorem atb_upd {Bl H H1 : BitVec 64} {L : GA} (h : ATB Bl H H1 L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "bloom" ≠ x) (h2 : ofString "entry" ≠ x) (h3 : ofString "n" ≠ x) (h4 : ofString "mark" ≠ x)
    (h5 : ofString "h" ≠ x) : ATB Bl H H1 (L.update (x,v)) :=
  let ⟨⟨⟨hb,⟨E,he⟩,⟨N,hn⟩⟩,hm⟩,hh⟩ := h
  ⟨⟨⟨by rw [lookup_update_ne' _ _ h1]; exact hb,⟨E,by rw [lookup_update_ne' _ _ h2]; exact he⟩,
    ⟨N,by rw [lookup_update_ne' _ _ h3]; exact hn⟩⟩,by rw [lookup_update_ne' _ _ h4]; exact hm⟩,
    by rw [lookup_update_ne' _ _ h5]; exact hh⟩

theorem atb_res {Bl H H1 : BitVec 64} {L : GA} (h : ATB Bl H H1 L) (x : MlS) (o : Option (ValueHOL 64))
    (h1 : ofString "bloom" ≠ x) (h2 : ofString "entry" ≠ x) (h3 : ofString "n" ≠ x) (h4 : ofString "mark" ≠ x)
    (h5 : ofString "h" ≠ x) : ATB Bl H H1 (L.resVarEq (x,o)) :=
  let ⟨⟨⟨hb,⟨E,he⟩,⟨N,hn⟩⟩,hm⟩,hh⟩ := h
  ⟨⟨⟨by rw [resVarEq_lookup_ne' _ _ _ _ h1]; exact hb,⟨E,by rw [resVarEq_lookup_ne' _ _ _ _ h2]; exact he⟩,
    ⟨N,by rw [resVarEq_lookup_ne' _ _ _ _ h3]; exact hn⟩⟩,by rw [resVarEq_lookup_ne' _ _ _ _ h4]; exact hm⟩,
    by rw [resVarEq_lookup_ne' _ _ _ _ h5]; exact hh⟩

section atb
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- The bit-setting loop of `add_to_bloom`: every byte store is at `bloom + (x >>> 3)`, at or above `bloom`. -/
theorem atbLoop_wn (Lo Sc Bl H H1 : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (hBl : Lo.toNat ≤ Bl.toNat) (hBlE : Bl.toNat + 2 ^ 61 < 2 ^ 64) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => ATB Bl H H1 L ∧ RG Lo Sc G) (fun L _ G => ATB Bl H H1 L ∧ RG Lo Sc G) (fun _ _ G => RG Lo Sc G)
      (.while (.cmp .less (.var .local (ofString "idx")) (.const 6)) (.dec (ofString "bit") .one (.op .and [(.op .or [(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "h")),(.var .local (ofString "idx"))])) (.const 8)),(.loadByte (.op .add [(.var .local (ofString "h")),(.var .local (ofString "idx")),(.const 1)]))]),(.const 2047)]) (.dec (ofString "bit_index") .one (.op .sub [(.const 2047),(.var .local (ofString "bit"))]) (.dec (ofString "byte_index") .one (.shift .lsr (.var .local (ofString "bit_index")) (.const 3)) (.dec (ofString "bv") .one (.shift .lsl (.const 1) (.op .sub [(.const 7),(.op .and [(.var .local (ofString "bit_index")),(.const 7)])])) (.seq (.storeByte (.op .add [(.var .local (ofString "bloom")),(.var .local (ofString "byte_index"))]) (.op .or [(.loadByte (.op .add [(.var .local (ofString "bloom")),(.var .local (ofString "byte_index"))])),(.var .local (ofString "bv"))])) (.assign .local (ofString "idx") (.op .add [(.var .local (ofString "idx")),(.const 2)])))))))) := by
  let I := fun L (_ : Mem) G => ATB Bl H H1 L ∧ RG Lo Sc G
  refine aqgd_whileI _ ?_
  refine aqgd_dec (Pb := I) (Qb := I) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ pre _ _ _ => ⟨atb_upd pre.1.1 _ v (by decide) (by decide) (by decide) (by decide) (by decide),
      pre.1.2⟩) ?_ (fun _ _ _ _ _ _ _ q => ⟨atb_res q.1 _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      q.2⟩)
  refine aqgd_dec (Pb := fun L _ G => (ATB Bl H H1 L ∧ ∃ BX : BitVec 64,
      L.lookup (ofString "bit_index") = some (.val (.word BX))) ∧ RG Lo Sc G) (Qb := I) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ pre _ ev _ => ?_) ?_
    (fun _ _ _ _ _ _ _ q => ⟨atb_res q.1 _ _ (by decide) (by decide) (by decide) (by decide) (by decide),q.2⟩)
  · obtain ⟨y,rfl⟩ := ev_op_word s _ _ v ev
    exact ⟨⟨atb_upd pre.1 _ _ (by decide) (by decide) (by decide) (by decide) (by decide),y,lookup_update_eq' _ _ _⟩,
      pre.2⟩
  refine aqgd_dec (Pb := fun L _ G => (ATB Bl H H1 L ∧ ∃ BI : BitVec 64,
      L.lookup (ofString "byte_index") = some (.val (.word BI)) ∧ BI.toNat < 2 ^ 61) ∧ RG Lo Sc G) (Qb := I) _ _ _
    (fun h => h.elim) (fun s v _ _ _ ⟨⟨ab,BX,hbx⟩,rg⟩ _ ev _ => ?_) ?_
    (fun _ _ _ _ _ _ _ q => ⟨atb_res q.1 _ _ (by decide) (by decide) (by decide) (by decide) (by decide),q.2⟩)
  · simp [EV,evalHOLExact,hbx,wordShiftHOL] at ev
    subst ev
    refine ⟨⟨atb_upd ab _ _ (by decide) (by decide) (by decide) (by decide) (by decide),BX >>> 3,
      lookup_update_eq' _ _ _,?_⟩,rg⟩
    have := BX.isLt
    simp [BitVec.toNat_ushiftRight]; omega
  let I2 := fun L (_ : Mem) G => (ATB Bl H H1 L ∧ ∃ BI : BitVec 64,
      L.lookup (ofString "byte_index") = some (.val (.word BI)) ∧ BI.toNat < 2 ^ 61) ∧ RG Lo Sc G
  refine aqgd_dec (Pb := I2) (Qb := I) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ ⟨⟨ab,BI,hbi,lt⟩,rg⟩ _ _ _ => ⟨⟨atb_upd ab _ v (by decide) (by decide) (by decide) (by decide)
      (by decide),BI,by rw [lookup_update_ne' _ _ (by decide)]; exact hbi,lt⟩,rg⟩) ?_
    (fun _ _ _ _ _ _ _ q => ⟨atb_res q.1 _ _ (by decide) (by decide) (by decide) (by decide) (by decide),q.2⟩)
  refine aqgd_seq (aqgd_conseq (r_stbG (LP := fun L G => (ATB Bl H H1 L ∧ ∃ BI : BitVec 64,
      L.lookup (ofString "byte_index") = some (.val (.word BI)) ∧ BI.toNat < 2 ^ 61) ∧ RG Lo Sc G)
      (LQ := fun L G => ATB Bl H H1 L ∧ RG Lo Sc G) Lo hLo8 hw _ _ ?_) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ h => h)) ?_
  · intro F s _ ⟨⟨ab,BI,hbi,lt⟩,rg⟩
    have e : (Bl + BI).toNat = Bl.toNat + BI.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨Bl + BI,by simp [EV,evalHOLExact,evalListHOLExact,ab.1.1.1,hbi,wordOpHOL,wordOp,valueIsWord,valueWord],
      by omega,fun _ => ⟨ab,rg⟩⟩
  exact aqgd_assignLocal _ _ (fun s v _ _ pre _ _ =>
    ⟨atb_upd pre.1 _ v (by decide) (by decide) (by decide) (by decide) (by decide),pre.2⟩)

#print axioms atbLoop_wn

/-- The actual `add_to_bloom(bloom, entry, n)`: Keccak of the entry into a fresh block, six bloom bits set in the
bytes at or above `bloom`, heap released; `RG Lo Sc` kept. -/
theorem addToBloom_wn (Lo Sc K Pd Bl : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (hLo8 : Lo.toNat % 8 = 0) (hBl : Lo.toNat ≤ Bl.toNat)
    (hBlE : Bl.toNat + 2 ^ 61 < 2 ^ 64) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "bloom") = some (.val (.word Bl)) ∧
        (∃ E : BitVec 64, L.lookup (ofString "entry") = some (.val (.word E))) ∧
        (∃ N : BitVec 64, L.lookup (ofString "n") = some (.val (.word N)))) ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun _ _ G => RG Lo Sc G)
      (sourceFunctionBody Guest.guestFn_add_to_bloom) := by
  rw [atbBody_eq]; unfold atbBody
  let SA := fun L : GA => L.lookup (ofString "bloom") = some (.val (.word Bl)) ∧
    (∃ E : BitVec 64, L.lookup (ofString "entry") = some (.val (.word E))) ∧
    (∃ N : BitVec 64, L.lookup (ofString "n") = some (.val (.word N)))
  have sau : ∀ (x : MlS), ofString "bloom" ≠ x → ofString "entry" ≠ x → ofString "n" ≠ x → ∀ L v, SA L →
      SA (L.update (x,v)) := fun x h1 h2 h3 L v ⟨hb,⟨E,he⟩,⟨N,hn⟩⟩ =>
    ⟨by rw [lookup_update_ne' _ _ h1]; exact hb,⟨E,by rw [lookup_update_ne' _ _ h2]; exact he⟩,
      ⟨N,by rw [lookup_update_ne' _ _ h3]; exact hn⟩⟩
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
    exact ⟨⟨⟨sau _ (by decide) (by decide) (by decide) _ _ ls,lookup_update_eq' _ _ _⟩,hH⟩,hs⟩
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 32#64)) ∧ M = M0' ∧ HeapIs G H) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + (32#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => (ATB Bl H H L ∧ RG Lo Sc G) ∧ H.toNat + 32 ≤ 33806089496)
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
    exact ⟨⟨⟨⟨sau _ (by decide) (by decide) (by decide) _ _ ls,by rw [lookup_update_ne' _ _ (by decide)]; exact hm⟩,
      lookup_update_eq' _ _ _⟩,⟨H',hH',by omega⟩,scrIs_onlyHeap oh hs⟩,by omega⟩
  refine aqgd_pureE (fun hcap32 => ?_)
  have oH : ¬ MWin H 32 w := by simpa using mwin_aboveH (k := 0) hal (by omega) (by omega)
  -- keccak256(entry, n, h)
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := ATB Bl H H) (Rv := fun _ => True)
    (fun L => ∃ Pp N : BitVec 64, KL0 Pp N H L) _ _ _ _ _ originalRuntimeCode_keccak_lookup
    (keccakGP K Pd hK0 hPd0 oK oP H oH _)
    (fun s values callee rs ⟨⟨⟨_,⟨E,he⟩,⟨N,hn⟩⟩,_⟩,hh⟩ args lookup => by
      obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,he] at ev1; subst ev1
      simp [EV,evalHOLExact,hn] at ev2; subst ev2
      simp [EV,evalHOLExact,hh] at ev3; subst ev3
      have e := callee_eq originalRuntimeCode_keccak_lookup lookup
      exact ⟨E,N,by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),
        by rw [e]; simp (config := {decide := true})⟩)) ?_
  refine aqgd_dec (Pb := fun L _ G => ATB Bl H H L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ pre _ _ _ => ⟨atb_upd pre.1 _ v (by decide) (by decide) (by decide) (by decide) (by decide),pre.2⟩)
    ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  refine aqgd_seq (atbLoop_wn Lo Sc Bl H H hLo8 hw hBl hBlE) ?_
  refine aqgd_seq (relMark (LP := ATB Bl H H) Lo Sc H hP0 hcapH hal (fun L h => h.1.2) (fun G h => h.2)) ?_
  exact aqgd_return _ (fun _ _ _ _ _ ⟨_,hH,hs⟩ _ _ => ⟨⟨H,hH,hLoH⟩,hs⟩)

#print axioms addToBloom_wn
end atb
def lbBody : ProgHOL 64 :=
  (.seq (.call (some (none,none)) (ofString "memzero") [(.var .local (ofString "out")),(.const 256)]) (.dec (ofString "n") .one (.load .one (.op .add [(.var .local (ofString "logs")),(.const 8)])) (.dec (ofString "p") .one (.load .one (.op .add [(.var .local (ofString "logs")),(.const 0)])) (.dec (ofString "i") .one (.const 0) (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) (.dec (ofString "log") .one (.load .one (.op .add [(.var .local (ofString "p")),(.panop .mul [(.var .local (ofString "i")),(.const 8)])])) (.seq (.call (some (none,none)) (ofString "add_to_bloom") [(.var .local (ofString "out")),(.load .one (.op .add [(.var .local (ofString "log")),(.const 0)])),(.const 20)]) (.dec (ofString "nt") .one (.load .one (.op .add [(.var .local (ofString "log")),(.const 16)])) (.dec (ofString "j") .one (.const 0) (.seq (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "nt"))) (.seq (.call (some (none,none)) (ofString "add_to_bloom") [(.var .local (ofString "out")),(.op .add [(.load .one (.op .add [(.var .local (ofString "log")),(.const 8)])),(.panop .mul [(.var .local (ofString "j")),(.const 32)])]),(.const 32)]) (.assign .local (ofString "j") (.op .add [(.var .local (ofString "j")),(.const 1)])))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)])))))))) (.return (.const 0)))))))

theorem lbBody_eq : sourceFunctionBody Guest.guestFn_logs_bloom = lbBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_logs_bloom,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


section lb
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- `add_to_bloom(out, e, k)` at a call site with `out = Bl`, keeping any locals predicate and `RG Lo Sc`. -/
theorem atbCall (Lo Sc K Pd Bl : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (hLo8 : Lo.toNat % 8 = 0) (hBl : Lo.toNat ≤ Bl.toNat)
    (hBlE : Bl.toNat + 2 ^ 61 < 2 ^ 64) {LP : GA → Prop}
    (hout : ∀ L, LP L → L.lookup (ofString "out") = some (.val (.word Bl))) (e k : ExpHOL 64)
    {RR : ValueHOL 64 → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ RG Lo Sc G)
      (fun L _ G => LP L ∧ RG Lo Sc G) RR
      (.call (some (none,none)) (ofString "add_to_bloom") [.var .local (ofString "out"),e,k]) :=
  rcallK (GP := RG Lo Sc) (LP := LP) (Rv := fun _ => True)
    (fun L => L.lookup (ofString "bloom") = some (.val (.word Bl)) ∧
      (∃ E : BitVec 64, L.lookup (ofString "entry") = some (.val (.word E))) ∧
      (∃ N : BitVec 64, L.lookup (ofString "n") = some (.val (.word N)))) _ _ _ _ _ originalRuntimeCode_addToBloom_lookup
    (aqgd_conseq (addToBloom_wn Lo Sc K Pd Bl hK0 hPd0 hw oK oP hLo8 hBl hBlE) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs lp args lookup => by
      obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,_,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,hout _ lp] at ev1; subst ev1
      obtain ⟨_,a,b,_,rfl,rfl⟩ := entry3_words originalRuntimeCode_addToBloom_lookup lookup
      have e := callee_eq originalRuntimeCode_addToBloom_lookup lookup
      exact ⟨by rw [e]; simp (config := {decide := true}),⟨a,by rw [e]; simp (config := {decide := true})⟩,
        ⟨b,by rw [e]; simp (config := {decide := true})⟩⟩)

/-- The actual `logs_bloom(logs, out)`: the 256-byte bloom at `out = Bl` zeroed, then bits set per address and topic;
writes only at or above `Bl` and in the Keccak windows (watched form); `RG Lo Sc` kept. -/
theorem logsBloom_wn (Lo Sc K Pd Bl : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (hLo8 : Lo.toNat % 8 = 0) (hBl : Lo.toNat ≤ Bl.toNat)
    (hBlE : Bl.toNat + 2 ^ 61 < 2 ^ 64) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word Bl)) ∧ RG Lo Sc G)
      (fun _ _ _ => False) (fun _ _ G => RG Lo Sc G)
      (sourceFunctionBody Guest.guestFn_logs_bloom) := by
  rw [lbBody_eq]; unfold lbBody
  let LO := fun L : GA => L.lookup (ofString "out") = some (.val (.word Bl))
  let I := fun L (_ : Mem) G => LO L ∧ RG Lo Sc G
  have ou : ∀ (x : MlS), ofString "out" ≠ x → ∀ L v, LO L → LO (L.update (x,v)) :=
    fun x hx L v h => by show (L.update (x,v)).lookup _ = _; rw [lookup_update_ne' _ _ hx]; exact h
  have orr : ∀ (x : MlS), ofString "out" ≠ x → ∀ L o, LO L → LO (L.resVarEq (x,o)) :=
    fun x hx L o h => by show (L.resVarEq (x,o)).lookup _ = _; rw [resVarEq_lookup_ne' _ _ _ _ hx]; exact h
  have dk : ∀ (x : MlS), ofString "out" ≠ x → ∀ {body : ProgHOL 64} (init : ExpHOL 64)
      {Qb Q' : GA → Mem → GA → Prop},
      (∀ L o M G, Qb L M G → Q' (L.resVarEq (x,o)) M G) →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) I Qb (fun _ _ G => RG Lo Sc G) body →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) I Q' (fun _ _ G => RG Lo Sc G)
        (.dec x .one init body) :=
    fun x hx _ init _ _ hQ hb => aqgd_dec (Pb := I) _ _ _ (fun h => h.elim)
      (fun s v _ _ _ pre _ _ _ => ⟨ou x hx _ v pre.1,pre.2⟩) hb
      (fun _ _ _ _ _ _ _ q => hQ _ _ _ _ q)
  have keepI : ∀ (x : MlS), ofString "out" ≠ x → ∀ L o M G, I L M G → I (L.resVarEq (x,o)) M G :=
    fun x hx L o M G q => ⟨orr x hx _ _ q.1,q.2⟩
  have oBl : ¬ MWin Bl (256#64).toNat w := mwin_lo hLo8 hBl (by simp; omega) hw
  -- memzero(out, 256)
  refine aqgd_seq (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word Bl)) ∧ L.lookup (ofString "n") = some (.val (.word 256#64))) ∧
        M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G' = G0' ∧ ∀ x, ¬ MWin Bl (256#64).toNat x → M' x = M0' x)
    (Q := I) _ _ _ _ _ originalRuntimeCode_memzero_lookup (by simp)
    (fun _ M0' G0' _ => memzero_wn Bl 256#64 (by decide) oBl M0' G0') ?_ ?_) ?_
  · intro F s values callee rs _ H hG ⟨lo,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,lo] at ev1; subst ev1
    simp [EV,evalHOLExact] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_memzero_lookup lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lo,rg⟩ ⟨hG,_⟩
    subst hG
    exact ⟨lo,rg⟩
  have call := fun (e k : ExpHOL 64) => atbCall (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (J := J)
    (C := C) (SKB := SKB) (Nj := Nj) (w := w) (RR := fun _ _ G => RG Lo Sc G) Lo Sc K Pd Bl hK0 hPd0 hw oK oP hLo8
    hBl hBlE (LP := LO) (fun L h => h) e k
  refine dk (ofString "n") (by decide) _ (Qb := fun _ _ _ => False) (fun _ _ _ _ h => h.elim) ?_
  refine dk (ofString "p") (by decide) _ (Qb := fun _ _ _ => False) (fun _ _ _ _ h => h.elim) ?_
  refine dk (ofString "i") (by decide) _ (Qb := fun _ _ _ => False) (fun _ _ _ _ h => h.elim) ?_
  refine aqgd_seq (aqgd_whileI _ ?_) (aqgd_return _ (fun _ _ _ _ _ pre _ _ => pre.2))
  refine aqgd_conseq (P := I) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine dk (ofString "log") (by decide) _ (keepI _ (by decide)) ?_
  refine aqgd_seq (call _ _) ?_
  refine dk (ofString "nt") (by decide) _ (keepI _ (by decide)) ?_
  refine dk (ofString "j") (by decide) _ (keepI _ (by decide)) ?_
  refine aqgd_seq (aqgd_whileI _ ?_) ?_
  · refine aqgd_conseq (P := I) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
    exact aqgd_seq (call _ _) (aqgd_assignLocal _ _ (fun s v _ _ pre _ _ => ⟨ou _ (by decide) _ v pre.1,pre.2⟩))
  exact aqgd_assignLocal _ _ (fun s v _ _ pre _ _ => ⟨ou _ (by decide) _ v pre.1,pre.2⟩)

#print axioms logsBloom_wn
end lb

section cw
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `w = rlp_encode_bytes(cur, e2, e3)` (result-assigning): `cur + w ≤ DF + 8` after the call. -/
theorem cab_call {LP : GA → Prop} (cur : MlS) (hcw : cur ≠ ofString "w") (e2 e3 : ExpHOL 64)
    (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (hcur : ∀ L, LP L → ∃ Cv : BitVec 64, L.lookup cur = some (.val (.word Cv)) ∧ Lo.toNat ≤ Cv.toNat ∧
      Cv.toNat + 16 < 2 ^ 64)
    (hup : ∀ L v, LP L → LP (L.update (ofString "w",v))) :
    AQGD D B A w (fun _ => False) (fun L _ _ => LP L)
      (fun L _ _ => LP L ∧ ∃ Cv R : BitVec 64, L.lookup cur = some (.val (.word Cv)) ∧
        L.lookup (ofString "w") = some (.val (.word R)) ∧ Cv.toNat + R.toNat ≤ DF + 8) RR
      (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes") [.var .local cur,e2,e3]) := by
  refine aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      ∃ Nn : BitVec 64, L.lookup (ofString "dst") = some (.val (.word (wordOf L0 cur))) ∧
        L.lookup (ofString "n") = some (.val (.word Nn)))
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => WRet DF (wordOf L0 cur) r)
    _ _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup (fun _ _ _ _ _ h => h.elim) (fun h => h) ?_ ?_ ?_
  · intro L0 _ _ lp
    obtain ⟨Cv,hc,lo,fit⟩ := hcur L0 lp
    rw [wordOf_eq hc]
    refine aqgd_exE (fun Nn => ?_)
    exact aqgd_conseq (encodeBytes_win (A := A) (B := B) hF hDF Lo hLo8 hw Cv Nn lo fit) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ G hG lp _ args lookup
    obtain ⟨Cv,hc,_,_⟩ := hcur _ lp
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,_,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,hc] at ev1; subst ev1
    obtain ⟨_,_,c3,_,_,rfl⟩ := entry3_words originalRuntimeCode_rlpEncodeBytes_lookup lookup
    have e := callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
    rw [wordOf_eq hc]
    exact ⟨c3,by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩
  · intro L _ _ v _ _ lp ⟨R,hr,hb⟩
    subst hr
    obtain ⟨Cv,hc,_,_⟩ := hcur _ lp
    rw [wordOf_eq hc] at hb
    exact ⟨hup _ _ lp,Cv,R,by rw [lookup_update_ne' _ _ hcw]; exact hc,lookup_update_eq' _ _ _,hb⟩

#print axioms cab_call

/-- `w = rlp_finish_list(d, cur)` (result-assigning) with `d + 9 ≤ cur ≤ DF + 8`: `d + w ≤ DF + 8`. -/
theorem fl_call {LP : GA → Prop} (d cur : MlS) (hdw : d ≠ ofString "w") (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62)
    (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (hcur : ∀ L, LP L → ∃ Dv Cv : BitVec 64, L.lookup d = some (.val (.word Dv)) ∧
      L.lookup cur = some (.val (.word Cv)) ∧ Lo.toNat ≤ Dv.toNat ∧ Dv.toNat + 9 ≤ Cv.toNat ∧ Cv.toNat ≤ DF + 8)
    (hup : ∀ L v, LP L → LP (L.update (ofString "w",v))) :
    AQGD D B A w (fun _ => False) (fun L _ _ => LP L)
      (fun L _ _ => LP L ∧ ∃ Dv R : BitVec 64, L.lookup d = some (.val (.word Dv)) ∧
        L.lookup (ofString "w") = some (.val (.word R)) ∧ Dv.toNat + R.toNat ≤ DF + 8) RR
      (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_finish_list") [.var .local d,.var .local cur]) := by
  refine aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      L.lookup (ofString "dst") = some (.val (.word (wordOf L0 d))) ∧
        L.lookup (ofString "payload_end") = some (.val (.word (wordOf L0 cur))))
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => WRet DF (wordOf L0 d) r)
    _ _ _ _ _ _ originalRuntimeCode_rlpFinishList_lookup (fun _ _ _ _ _ h => h.elim) (fun h => h) ?_ ?_ ?_
  · intro L0 _ _ lp
    obtain ⟨Dv,Cv,hd,hc,lo,h9,hi⟩ := hcur L0 lp
    rw [wordOf_eq hd,wordOf_eq hc]
    exact aqgd_conseq (finishList_win (A := A) (B := B) hF hDF Lo hLo8 hw Dv Cv lo h9 hi) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ G hG lp _ args lookup
    obtain ⟨Dv,Cv,hd,hc,_⟩ := hcur _ lp
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,hd] at ev1; subst ev1
    simp [EV,evalHOLExact,hc] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_rlpFinishList_lookup lookup
    rw [wordOf_eq hd,wordOf_eq hc]
    exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩
  · intro L _ _ v _ _ lp ⟨R,hr,hb⟩
    subst hr
    obtain ⟨Dv,Cv,hd,_⟩ := hcur _ lp
    rw [wordOf_eq hd] at hb
    exact ⟨hup _ _ lp,Dv,R,by rw [lookup_update_ne' _ _ hdw]; exact hd,lookup_update_eq' _ _ _,hb⟩

#print axioms fl_call
end cw

/-- Outer-loop state of `encode_logs`: `dst = Dst`, `q = Q` with `Dst + 9 ≤ Q ≤ DF + 17`. -/
def ELO (Dst : BitVec 64) (DF : Nat) (L : GA) : Prop :=
  L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ ∃ Q : BitVec 64, L.lookup (ofString "q") = some (.val (.word Q)) ∧
    Dst.toNat + 9 ≤ Q.toNat ∧ Q.toNat ≤ DF + 17

theorem elo_upd {Dst : BitVec 64} {DF : Nat} {L : GA} (h : ELO Dst DF L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "dst" ≠ x) (h2 : ofString "q" ≠ x) : ELO Dst DF (L.update (x,v)) :=
  let ⟨hd,Q,hq,a,b⟩ := h
  ⟨by rw [lookup_update_ne' _ _ h1]; exact hd,Q,by rw [lookup_update_ne' _ _ h2]; exact hq,a,b⟩

theorem elo_res {Dst : BitVec 64} {DF : Nat} {L : GA} (h : ELO Dst DF L) (x : MlS) (o : Option (ValueHOL 64))
    (h1 : ofString "dst" ≠ x) (h2 : ofString "q" ≠ x) : ELO Dst DF (L.resVarEq (x,o)) :=
  let ⟨hd,Q,hq,a,b⟩ := h
  ⟨by rw [resVarEq_lookup_ne' _ _ _ _ h1]; exact hd,Q,by rw [resVarEq_lookup_ne' _ _ _ _ h2]; exact hq,a,b⟩

def elBody : ProgHOL 64 :=
  (.dec (ofString "n") .one (.load .one (.op .add [(.var .local (ofString "logs")),(.const 8)])) (.dec (ofString "p") .one (.load .one (.op .add [(.var .local (ofString "logs")),(.const 0)])) (.dec (ofString "q") .one (.op .add [(.var .local (ofString "dst")),(.const 9)]) (.dec (ofString "i") .one (.const 0) (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) (.dec (ofString "log") .one (.load .one (.op .add [(.var .local (ofString "p")),(.panop .mul [(.var .local (ofString "i")),(.const 8)])])) (.dec (ofString "r") .one (.op .add [(.var .local (ofString "q")),(.const 9)]) (.decCall (ofString "w") .one (ofString "rlp_encode_bytes") [(.var .local (ofString "r")),(.load .one (.op .add [(.var .local (ofString "log")),(.const 0)])),(.const 20)] (.seq (.assign .local (ofString "r") (.op .add [(.var .local (ofString "r")),(.var .local (ofString "w"))])) (.dec (ofString "tstart") .one (.var .local (ofString "r")) (.dec (ofString "t") .one (.op .add [(.var .local (ofString "r")),(.const 9)]) (.dec (ofString "nt") .one (.load .one (.op .add [(.var .local (ofString "log")),(.const 16)])) (.dec (ofString "j") .one (.const 0) (.seq (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "nt"))) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_bytes") [(.var .local (ofString "t")),(.op .add [(.load .one (.op .add [(.var .local (ofString "log")),(.const 8)])),(.panop .mul [(.var .local (ofString "j")),(.const 32)])]),(.const 32)]) (.seq (.assign .local (ofString "t") (.op .add [(.var .local (ofString "t")),(.var .local (ofString "w"))])) (.assign .local (ofString "j") (.op .add [(.var .local (ofString "j")),(.const 1)]))))) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_finish_list") [(.var .local (ofString "tstart")),(.var .local (ofString "t"))]) (.seq (.assign .local (ofString "r") (.op .add [(.var .local (ofString "tstart")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_bytes") [(.var .local (ofString "r")),(.load .one (.op .add [(.var .local (ofString "log")),(.const 24)])),(.load .one (.op .add [(.var .local (ofString "log")),(.const 32)]))]) (.seq (.assign .local (ofString "r") (.op .add [(.var .local (ofString "r")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_finish_list") [(.var .local (ofString "q")),(.var .local (ofString "r"))]) (.seq (.assign .local (ofString "q") (.op .add [(.var .local (ofString "q")),(.var .local (ofString "w"))])) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)])))))))))))))))))) (.decCall (ofString "total") .one (ofString "rlp_finish_list") [(.var .local (ofString "dst")),(.var .local (ofString "q"))] (.return (.var .local (ofString "total")))))))))

theorem elBody_eq : sourceFunctionBody Guest.guestFn_encode_logs = elBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_encode_logs,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


section el
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- One iteration of the outer `encode_logs` loop keeps `ELO`. -/
theorem elIter (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dst : BitVec 64) (hLD : Lo.toNat ≤ Dst.toNat) :
    AQGD D B A w (fun _ => False) (fun L _ _ => ELO Dst DF L ∧ True) (fun L _ _ => ELO Dst DF L) RR
      (.dec (ofString "log") .one (.load .one (.op .add [(.var .local (ofString "p")),(.panop .mul [(.var .local (ofString "i")),(.const 8)])])) (.dec (ofString "r") .one (.op .add [(.var .local (ofString "q")),(.const 9)]) (.decCall (ofString "w") .one (ofString "rlp_encode_bytes") [(.var .local (ofString "r")),(.load .one (.op .add [(.var .local (ofString "log")),(.const 0)])),(.const 20)] (.seq (.assign .local (ofString "r") (.op .add [(.var .local (ofString "r")),(.var .local (ofString "w"))])) (.dec (ofString "tstart") .one (.var .local (ofString "r")) (.dec (ofString "t") .one (.op .add [(.var .local (ofString "r")),(.const 9)]) (.dec (ofString "nt") .one (.load .one (.op .add [(.var .local (ofString "log")),(.const 16)])) (.dec (ofString "j") .one (.const 0) (.seq (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "nt"))) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_bytes") [(.var .local (ofString "t")),(.op .add [(.load .one (.op .add [(.var .local (ofString "log")),(.const 8)])),(.panop .mul [(.var .local (ofString "j")),(.const 32)])]),(.const 32)]) (.seq (.assign .local (ofString "t") (.op .add [(.var .local (ofString "t")),(.var .local (ofString "w"))])) (.assign .local (ofString "j") (.op .add [(.var .local (ofString "j")),(.const 1)]))))) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_finish_list") [(.var .local (ofString "tstart")),(.var .local (ofString "t"))]) (.seq (.assign .local (ofString "r") (.op .add [(.var .local (ofString "tstart")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_bytes") [(.var .local (ofString "r")),(.load .one (.op .add [(.var .local (ofString "log")),(.const 24)])),(.load .one (.op .add [(.var .local (ofString "log")),(.const 32)]))]) (.seq (.assign .local (ofString "r") (.op .add [(.var .local (ofString "r")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_finish_list") [(.var .local (ofString "q")),(.var .local (ofString "r"))]) (.seq (.assign .local (ofString "q") (.op .add [(.var .local (ofString "q")),(.var .local (ofString "w"))])) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)]))))))))))))))))) := by
  have hF9 : Fence D (DF + 9) := fence_mono hF (by omega)
  have hDF0 : DF ≤ 2 ^ 62 := by omega
  -- log
  refine r_dec (LB := ELO Dst DF) (LQ' := ELO Dst DF) _ _ _ (fun h => h.elim)
    (fun s v _ h ev => elo_upd h.1 _ v (by decide) (by decide)) ?_
    (fun _ _ _ q => elo_res q _ _ (by decide) (by decide))
  -- r = q + 9
  let S1 := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ ∃ Q : BitVec 64,
    L.lookup (ofString "q") = some (.val (.word Q)) ∧ Dst.toNat + 9 ≤ Q.toNat ∧ Q.toNat ≤ DF + 17 ∧
    L.lookup (ofString "r") = some (.val (.word (Q + 9#64)))
  refine r_dec (LB := S1) (LQ' := ELO Dst DF) _ _ _ (fun h => h.elim) (fun s v _ ⟨hd,Q,hq,a,b⟩ ev => ?_) ?_
    (fun _ _ _ q => elo_res q _ _ (by decide) (by decide))
  · simp [EV,evalHOLExact,evalListHOLExact,hq,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q,by rw [lookup_update_ne' _ _ (by decide)]; exact hq,
      a,b,lookup_update_eq' _ _ _⟩
  -- w = rlp_encode_bytes(r, lds (log + 0), 20)
  let S2 := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ ∃ Q : BitVec 64,
    L.lookup (ofString "q") = some (.val (.word Q)) ∧ Dst.toNat + 9 ≤ Q.toNat ∧ Q.toNat ≤ DF + 17 ∧
    ∃ R1 : BitVec 64, L.lookup (ofString "r") = some (.val (.word R1)) ∧ Q.toNat + 9 ≤ R1.toNat ∧ R1.toNat ≤ DF + 8
  refine aqgd_decCallSpecF
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      ∃ Nn : BitVec 64, L.lookup (ofString "dst") = some (.val (.word (wordOf L0 (ofString "r")))) ∧
        L.lookup (ofString "n") = some (.val (.word Nn)))
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => WRet DF (wordOf L0 (ofString "r")) r)
    (Pc := fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ ∃ Q : BitVec 64,
      L.lookup (ofString "q") = some (.val (.word Q)) ∧ Dst.toNat + 9 ≤ Q.toNat ∧ Q.toNat ≤ DF + 17 ∧
      ∃ R0 W : BitVec 64, L.lookup (ofString "r") = some (.val (.word R0)) ∧
        L.lookup (ofString "w") = some (.val (.word W)) ∧ Q.toNat + 9 ≤ R0.toNat ∧ R0.toNat + W.toNat ≤ DF + 8)
    (Qc := fun L _ _ => ELO Dst DF L) _ _ _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup ?_ ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ q => elo_res q _ _ (by decide) (by decide))
  · intro L0 _ _ ⟨_,Q,_,a,b,hr⟩
    rw [wordOf_eq hr]
    have e : (Q + 9#64).toNat = Q.toNat + 9 := by simp [BitVec.toNat_add]; omega
    exact aqgd_exE (fun Nn => aqgd_conseq (encodeBytes_win (A := A) (B := B) hF hDF0 Lo hLo8 hw (Q + 9#64) Nn
      (by omega) (by omega)) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
  · intro F s values callee rs _ G hG ⟨_,Q,_,_,_,hr⟩ _ args lookup
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,hr] at ev1; subst ev1
    simp [EV,evalHOLExact] at ev3; subst ev3
    have e := callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
    rw [wordOf_eq hr]
    exact ⟨20#64,by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩
  · intro L _ _ v _ _ ⟨hd,Q,hq,a,b,hr⟩ ⟨W,hw',hb⟩ _
    subst hw'
    rw [wordOf_eq hr] at hb
    have e : (Q + 9#64).toNat = Q.toNat + 9 := by simp [BitVec.toNat_add]; omega
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q,by rw [lookup_update_ne' _ _ (by decide)]; exact hq,
      a,b,Q + 9#64,W,by rw [lookup_update_ne' _ _ (by decide)]; exact hr,lookup_update_eq' _ _ _,by omega,hb⟩
  -- r = r + w
  refine aqgd_seq (aqgd_assignLocal (Q := fun L _ _ => S2 L) _ _ (fun s v _ _ ⟨hd,Q,hq,a,b,R0,W,hr,hw',c,d⟩ _ ev => ?_)) ?_
  · simp [EV,evalHOLExact,evalListHOLExact,hr,hw',wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have e : (R0 + W).toNat = R0.toNat + W.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q,by rw [lookup_update_ne' _ _ (by decide)]; exact hq,
      a,b,R0 + W,lookup_update_eq' _ _ _,by omega,by omega⟩
  -- tstart = r; t = r + 9
  let S4 := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ ∃ Q : BitVec 64,
    L.lookup (ofString "q") = some (.val (.word Q)) ∧ Dst.toNat + 9 ≤ Q.toNat ∧ Q.toNat ≤ DF + 17 ∧
    ∃ R1 : BitVec 64, L.lookup (ofString "tstart") = some (.val (.word R1)) ∧ Q.toNat + 9 ≤ R1.toNat ∧
      R1.toNat ≤ DF + 8 ∧ ∃ Tv : BitVec 64, L.lookup (ofString "t") = some (.val (.word Tv)) ∧
        R1.toNat + 9 ≤ Tv.toNat ∧ Tv.toNat ≤ DF + 17
  have s4u : ∀ (x : MlS), ofString "dst" ≠ x → ofString "q" ≠ x → ofString "tstart" ≠ x → ofString "t" ≠ x →
      ∀ L v, S4 L → S4 (L.update (x,v)) := fun x h1 h2 h3 h4 L v ⟨hd,Q,hq,a,b,R1,ht,c,d,Tv,htv,e,f⟩ =>
    ⟨by rw [lookup_update_ne' _ _ h1]; exact hd,Q,by rw [lookup_update_ne' _ _ h2]; exact hq,a,b,R1,
      by rw [lookup_update_ne' _ _ h3]; exact ht,c,d,Tv,by rw [lookup_update_ne' _ _ h4]; exact htv,e,f⟩
  refine r_dec (LB := fun L => S2 L ∧ ∃ R1 : BitVec 64, L.lookup (ofString "r") = some (.val (.word R1)) ∧
      L.lookup (ofString "tstart") = some (.val (.word R1))) (LQ' := ELO Dst DF) _ _ _ (fun h => h.elim)
    (fun s v _ ⟨hd,Q,hq,a,b,R1,hr,c,d⟩ ev => ?_) ?_ (fun _ _ _ q => elo_res q _ _ (by decide) (by decide))
  · simp [EV,evalHOLExact,hr] at ev
    subst ev
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q,by rw [lookup_update_ne' _ _ (by decide)]; exact hq,
      a,b,R1,by rw [lookup_update_ne' _ _ (by decide)]; exact hr,c,d⟩,R1,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hr,lookup_update_eq' _ _ _⟩
  refine r_dec (LB := S4) (LQ' := ELO Dst DF) _ _ _ (fun h => h.elim)
    (fun s v _ ⟨⟨hd,Q,hq,a,b,R1,hr,c,d⟩,R1',hr',ht⟩ ev => ?_) ?_ (fun _ _ _ q => elo_res q _ _ (by decide) (by decide))
  · rw [hr] at hr'
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hr'
    subst hr'
    simp [EV,evalHOLExact,evalListHOLExact,hr,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have e : (R1 + 9#64).toNat = R1.toNat + 9 := by simp [BitVec.toNat_add]; omega
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q,by rw [lookup_update_ne' _ _ (by decide)]; exact hq,
      a,b,R1,by rw [lookup_update_ne' _ _ (by decide)]; exact ht,c,d,R1 + 9#64,lookup_update_eq' _ _ _,by omega,
      by omega⟩
  -- nt, j
  refine r_dec (LB := S4) (LQ' := ELO Dst DF) _ _ _ (fun h => h.elim)
    (fun s v _ h _ => s4u _ (by decide) (by decide) (by decide) (by decide) _ _ h) ?_
    (fun _ _ _ q => elo_res q _ _ (by decide) (by decide))
  refine r_dec (LB := S4) (LQ' := ELO Dst DF) _ _ _ (fun h => h.elim)
    (fun s v _ h _ => s4u _ (by decide) (by decide) (by decide) (by decide) _ _ h) ?_
    (fun _ _ _ q => elo_res q _ _ (by decide) (by decide))
  -- inner topic loop
  have lot : ∀ L, S4 L → ∃ Cv : BitVec 64, L.lookup (ofString "t") = some (.val (.word Cv)) ∧ Lo.toNat ≤ Cv.toNat ∧
      Cv.toNat + 16 < 2 ^ 64 := fun L ⟨_,Q,_,a,b,R1,_,c,d,Tv,ht,e,f⟩ => ⟨Tv,ht,by omega,by omega⟩
  refine aqgd_seq (r_while (LI := S4) (LC := fun _ => True) _ (fun _ _ _ _ _ _ => trivial) ?_) ?_
  · refine aqgd_conseq (P := fun L _ _ => S4 L) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_seq (cab_call (LP := S4) (ofString "t") (by decide) _ _ hF hDF0 Lo hLo8 hw lot
      (fun L v h => s4u _ (by decide) (by decide) (by decide) (by decide) _ _ h)) ?_
    refine aqgd_seq (aqgd_assignLocal (Q := fun L _ _ => S4 L) _ _
      (fun s v _ _ ⟨⟨hd,Q,hq,a,b,R1,ht,c,d,Tv,htv,e,f⟩,Cv,R,hc,hw',hb⟩ _ ev => ?_)) ?_
    · simp [EV,evalHOLExact,evalListHOLExact,hc,hw',wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      rw [htv] at hc
      simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hc
      subst hc
      have e2 : (Tv + R).toNat = Tv.toNat + R.toNat := by simp [BitVec.toNat_add]; omega
      exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q,by rw [lookup_update_ne' _ _ (by decide)]; exact hq,
        a,b,R1,by rw [lookup_update_ne' _ _ (by decide)]; exact ht,c,d,Tv + R,lookup_update_eq' _ _ _,by omega,
        by omega⟩
    exact aqgd_assignLocal _ _ (fun s v _ _ h _ _ => s4u _ (by decide) (by decide) (by decide) (by decide) _ _ h)
  -- w = rlp_finish_list(tstart, t) (fence widened by 9)
  refine aqgd_seq (fl_call (LP := S4) (ofString "tstart") (ofString "t") (by decide) hF9 (by omega) Lo hLo8 hw
    (fun L ⟨_,Q,_,a,b,R1,ht,c,d,Tv,htv,e,f⟩ => ⟨R1,Tv,ht,htv,by omega,e,by omega⟩)
    (fun L v h => s4u _ (by decide) (by decide) (by decide) (by decide) _ _ h)) ?_
  -- r = tstart + w
  let S5 := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ ∃ Q : BitVec 64,
    L.lookup (ofString "q") = some (.val (.word Q)) ∧ Dst.toNat + 9 ≤ Q.toNat ∧ Q.toNat ≤ DF + 17 ∧
    ∃ R2 : BitVec 64, L.lookup (ofString "r") = some (.val (.word R2)) ∧ Q.toNat + 9 ≤ R2.toNat ∧ R2.toNat ≤ DF + 17
  have s5u : ∀ (x : MlS), ofString "dst" ≠ x → ofString "q" ≠ x → ofString "r" ≠ x →
      ∀ L v, S5 L → S5 (L.update (x,v)) := fun x h1 h2 h3 L v ⟨hd,Q,hq,a,b,R2,hr,c,d⟩ =>
    ⟨by rw [lookup_update_ne' _ _ h1]; exact hd,Q,by rw [lookup_update_ne' _ _ h2]; exact hq,a,b,R2,
      by rw [lookup_update_ne' _ _ h3]; exact hr,c,d⟩
  refine aqgd_seq (aqgd_assignLocal (Q := fun L _ _ => S5 L) _ _
    (fun s v _ _ ⟨⟨hd,Q,hq,a,b,R1,ht,c,d,_⟩,Dv,R,hdv,hw',hb⟩ _ ev => ?_)) ?_
  · rw [ht] at hdv
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hdv
    subst hdv
    simp [EV,evalHOLExact,evalListHOLExact,ht,hw',wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have e2 : (R1 + R).toNat = R1.toNat + R.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q,by rw [lookup_update_ne' _ _ (by decide)]; exact hq,
      a,b,R1 + R,lookup_update_eq' _ _ _,by omega,by omega⟩
  -- w = rlp_encode_bytes(r, lds (log + 24), lds (log + 32))
  refine aqgd_seq (cab_call (LP := S5) (ofString "r") (by decide) _ _ hF hDF0 Lo hLo8 hw
    (fun L ⟨_,Q,_,a,b,R2,hr,c,d⟩ => ⟨R2,hr,by omega,by omega⟩)
    (fun L v h => s5u _ (by decide) (by decide) (by decide) _ _ h)) ?_
  -- r = r + w
  let S6 := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ ∃ Q : BitVec 64,
    L.lookup (ofString "q") = some (.val (.word Q)) ∧ Dst.toNat + 9 ≤ Q.toNat ∧ Q.toNat ≤ DF + 17 ∧
    ∃ R3 : BitVec 64, L.lookup (ofString "r") = some (.val (.word R3)) ∧ Q.toNat + 9 ≤ R3.toNat ∧ R3.toNat ≤ DF + 8
  refine aqgd_seq (aqgd_assignLocal (Q := fun L _ _ => S6 L) _ _
    (fun s v _ _ ⟨⟨hd,Q,hq,a,b,R2,hr,c,d⟩,Cv,R,hc,hw',hb⟩ _ ev => ?_)) ?_
  · rw [hr] at hc
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hc
    subst hc
    simp [EV,evalHOLExact,evalListHOLExact,hr,hw',wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have e2 : (R2 + R).toNat = R2.toNat + R.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q,by rw [lookup_update_ne' _ _ (by decide)]; exact hq,
      a,b,R2 + R,lookup_update_eq' _ _ _,by omega,by omega⟩
  -- w = rlp_finish_list(q, r)
  refine aqgd_seq (fl_call (LP := S6) (ofString "q") (ofString "r") (by decide) hF hDF0 Lo hLo8 hw
    (fun L ⟨_,Q,hq,a,b,R3,hr,c,d⟩ => ⟨Q,R3,hq,hr,by omega,c,d⟩)
    (fun L v ⟨hd,Q,hq,a,b,R3,hr,c,d⟩ => ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hq,a,b,R3,by rw [lookup_update_ne' _ _ (by decide)]; exact hr,
      c,d⟩)) ?_
  -- q = q + w
  refine aqgd_seq (aqgd_assignLocal (Q := fun L _ _ => ELO Dst DF L) _ _
    (fun s v _ _ ⟨⟨hd,Q,hq,a,b,_⟩,Dv,R,hdv,hw',hb⟩ _ ev => ?_)) ?_
  · rw [hq] at hdv
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hdv
    subst hdv
    simp [EV,evalHOLExact,evalListHOLExact,hq,hw',wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have e2 : (Q + R).toNat = Q.toNat + R.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,Q + R,lookup_update_eq' _ _ _,by omega,by omega⟩
  exact aqgd_assignLocal _ _ (fun s v _ _ h _ _ => elo_upd h _ v (by decide) (by decide))

#print axioms elIter

/-- The actual `encode_logs(dst, logs)` with `Lo ≤ dst ≤ DF + 8`: writes only at or above `dst`, returns `R` with
`dst + R ≤ DF + 17` (`WRet (DF + 9)`). -/
theorem encodeLogs_win (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dst : BitVec 64) (hLD : Lo.toNat ≤ Dst.toNat) (hD8 : Dst.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)))
      (fun _ _ _ => False) (fun r _ _ => WRet (DF + 9) Dst r) (sourceFunctionBody Guest.guestFn_encode_logs) := by
  rw [elBody_eq]; unfold elBody
  have hF9 : Fence D (DF + 9) := fence_mono hF (by omega)
  let LD := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst))
  have ldu : ∀ (x : MlS), ofString "dst" ≠ x → ∀ L v, LD L → LD (L.update (x,v)) :=
    fun x hx L v h => by show (L.update (x,v)).lookup _ = _; rw [lookup_update_ne' _ _ hx]; exact h
  refine r_dec (LB := LD) (LQ' := fun _ => False) _ _ _ (fun h => h.elim) (fun s v _ h _ => ldu _ (by decide) _ _ h) ?_
    (fun _ _ _ h => h)
  refine r_dec (LB := LD) (LQ' := fun _ => False) _ _ _ (fun h => h.elim) (fun s v _ h _ => ldu _ (by decide) _ _ h) ?_
    (fun _ _ _ h => h)
  refine r_dec (LB := ELO Dst DF) (LQ' := fun _ => False) _ _ _ (fun h => h.elim) (fun s v _ h ev => ?_) ?_
    (fun _ _ _ h => h)
  · have h' : s.locals.lookup (ofString "dst") = some (.val (.word Dst)) := h
    simp [EV,evalHOLExact,evalListHOLExact,h',wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have e : (Dst + 9#64).toNat = Dst.toNat + 9 := by simp [BitVec.toNat_add]; omega
    exact ⟨ldu _ (by decide) _ _ h,Dst + 9#64,lookup_update_eq' _ _ _,by omega,by omega⟩
  refine r_dec (LB := ELO Dst DF) (LQ' := fun _ => False) _ _ _ (fun h => h.elim)
    (fun s v _ h _ => elo_upd h _ v (by decide) (by decide)) ?_ (fun _ _ _ h => h)
  refine aqgd_seq (r_while (LI := ELO Dst DF) (LC := fun _ => True) _ (fun _ _ _ _ _ _ => trivial)
    (elIter hF hDF Lo hLo8 hw Dst hLD)) ?_
  refine aqgd_decCallSpecF
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "payload_end") = some (.val (.word (wordOf L0 (ofString "q")))))
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => WRet (DF + 9) Dst r)
    (Pc := fun L _ _ => ∃ R : BitVec 64, L.lookup (ofString "total") = some (.val (.word R)) ∧
      Dst.toNat + R.toNat ≤ DF + 9 + 8)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_rlpFinishList_lookup ?_ ?_ (fun h => h.elim) ?_
    (aqgd_return _ (fun s v _ _ _ ⟨R,hr,hb⟩ _ ev => by
      simp [EV,evalHOLExact,hr] at ev; subst ev; exact ⟨R,rfl,hb⟩)) (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L0 _ _ ⟨_,Q,hq,a,b⟩
    rw [wordOf_eq hq]
    exact aqgd_conseq (finishList_win (A := A) (B := B) hF9 (by omega) Lo hLo8 hw Dst Q hLD a (by omega))
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ G hG ⟨hd,Q,hq,_⟩ _ args lookup
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,hd] at ev1; subst ev1
    simp [EV,evalHOLExact,hq] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_rlpFinishList_lookup lookup
    rw [wordOf_eq hq]
    exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩
  · intro L _ _ v _ _ _ ⟨R,hr,hb⟩ _
    subst hr
    exact ⟨R,lookup_update_eq' _ _ _,hb⟩

#print axioms encodeLogs_win
end el

section cw2
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `w = rlp_encode_word(cur, e2)` (result-assigning): `cur + w ≤ DF + 8` after the call. -/
theorem cew_call {LP : GA → Prop} (cur : MlS) (hcw : cur ≠ ofString "w") (e2 : ExpHOL 64)
    (hF : Fence D DF) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (hcur : ∀ L, LP L → ∃ Cv : BitVec 64, L.lookup cur = some (.val (.word Cv)) ∧ Lo.toNat ≤ Cv.toNat ∧
      Cv.toNat + 16 < 2 ^ 64)
    (hup : ∀ L v, LP L → LP (L.update (ofString "w",v))) :
    AQGD D B A w (fun _ => False) (fun L _ _ => LP L)
      (fun L _ _ => LP L ∧ ∃ Cv R : BitVec 64, L.lookup cur = some (.val (.word Cv)) ∧
        L.lookup (ofString "w") = some (.val (.word R)) ∧ Cv.toNat + R.toNat ≤ DF + 8) RR
      (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_word") [.var .local cur,e2]) := by
  refine aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      ∃ W : BitVec 64, L.lookup (ofString "dst") = some (.val (.word (wordOf L0 cur))) ∧
        L.lookup (ofString "w") = some (.val (.word W)))
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => WRet DF (wordOf L0 cur) r)
    _ _ _ _ _ _ originalRuntimeCode_rlpEncodeWord_lookup (fun _ _ _ _ _ h => h.elim) (fun h => h) ?_ ?_ ?_
  · intro L0 _ _ lp
    obtain ⟨Cv,hc,lo,fit⟩ := hcur L0 lp
    rw [wordOf_eq hc]
    exact aqgd_exE (fun W => aqgd_conseq (encodeWord_win (A := A) (B := B) hF Lo hLo8 hw Cv W lo fit)
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => wret_of_hdr h))
  · intro F s values callee rs _ G hG lp _ args lookup
    obtain ⟨Cv,hc,_,_⟩ := hcur _ lp
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,hc] at ev1; subst ev1
    obtain ⟨_,c2,_,rfl⟩ := entry2_words originalRuntimeCode_rlpEncodeWord_lookup lookup
    have e := callee_eq originalRuntimeCode_rlpEncodeWord_lookup lookup
    rw [wordOf_eq hc]
    exact ⟨c2,by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩
  · intro L _ _ v _ _ lp ⟨R,hr,hb⟩
    subst hr
    obtain ⟨Cv,hc,_,_⟩ := hcur _ lp
    rw [wordOf_eq hc] at hb
    exact ⟨hup _ _ lp,Cv,R,by rw [lookup_update_ne' _ _ hcw]; exact hc,lookup_update_eq' _ _ _,hb⟩

#print axioms cew_call

/-- `w = encode_logs(cur, e2)` (result-assigning) with `Lo ≤ cur ≤ DF + 8`: `cur + w ≤ DF + 17` after the call. -/
theorem cel_call {LP : GA → Prop} (cur : MlS) (hcw : cur ≠ ofString "w") (e2 : ExpHOL 64)
    (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (hcur : ∀ L, LP L → ∃ Cv : BitVec 64, L.lookup cur = some (.val (.word Cv)) ∧ Lo.toNat ≤ Cv.toNat ∧
      Cv.toNat ≤ DF + 8)
    (hup : ∀ L v, LP L → LP (L.update (ofString "w",v))) :
    AQGD D B A w (fun _ => False) (fun L _ _ => LP L)
      (fun L _ _ => LP L ∧ ∃ Cv R : BitVec 64, L.lookup cur = some (.val (.word Cv)) ∧
        L.lookup (ofString "w") = some (.val (.word R)) ∧ Cv.toNat + R.toNat ≤ DF + 9 + 8) RR
      (.call (some (some (.local,ofString "w"),none)) (ofString "encode_logs") [.var .local cur,e2]) := by
  refine aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      L.lookup (ofString "dst") = some (.val (.word (wordOf L0 cur))))
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => WRet (DF + 9) (wordOf L0 cur) r)
    _ _ _ _ _ _ originalRuntimeCode_encodeLogs_lookup (fun _ _ _ _ _ h => h.elim) (fun h => h) ?_ ?_ ?_
  · intro L0 _ _ lp
    obtain ⟨Cv,hc,lo,hi⟩ := hcur L0 lp
    rw [wordOf_eq hc]
    exact aqgd_conseq (encodeLogs_win (A := A) (B := B) hF hDF Lo hLo8 hw Cv lo hi)
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ G hG lp _ args lookup
    obtain ⟨Cv,hc,_,_⟩ := hcur _ lp
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,hc] at ev1; subst ev1
    have e := callee_eq originalRuntimeCode_encodeLogs_lookup lookup
    rw [wordOf_eq hc]
    rw [e]; simp (config := {decide := true})
  · intro L _ _ v _ _ lp ⟨R,hr,hb⟩
    subst hr
    obtain ⟨Cv,hc,_,_⟩ := hcur _ lp
    rw [wordOf_eq hc] at hb
    exact ⟨hup _ _ lp,Cv,R,by rw [lookup_update_ne' _ _ hcw]; exact hc,lookup_update_eq' _ _ _,hb⟩

#print axioms cel_call
end cw2

section rga
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `name = alloc(e)` (any size expression) over the pinned-journal arena keeping `RG Lo Sc`: the new block
`X ≥ Lo`, `X ≤ HEAP_END`, 8-aligned. -/
theorem rg_alloc {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name : MlS) (e : ExpHOL 64) {cont : ProgHOL 64}
    (Lo Sc : BitVec 64)
    (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, EV s e = some x → ∃ y : BitVec 64, x = .val (.word y))
    (hup : ∀ L (X : BitVec 64), LP L → Lo.toNat ≤ X.toNat → X.toNat ≤ 33806089496 → X.toNat % 8 = 0 →
      LP' (L.update (name,.val (.word X))))
    (hcont : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP' L ∧ RG Lo Sc G) Q RR cont)
    (hres : ∀ (L : GA) (M : Mem) (G : GA) (L' : GA) (M' : Mem) (G' : GA), LP L ∧ RG Lo Sc G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ RG Lo Sc G) Q2 RR
      (.decCall name .one (ofString "alloc") [e] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ Nn : BitVec 64, L.lookup (ofString "n") = some (.val (.word Nn))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ Nn : BitVec 64, (v = .val (.word (hpOf G0')) ∧ M' = M0' ∧ (hpOf G0').toNat % 8 = 0 ∧
        ∃ H' : BitVec 64, HeapIs G' H' ∧ (hpOf G0').toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧
          OnlyHeap G0' G')
    (Pc := fun L _ G => LP' L ∧ RG Lo Sc G) (Qc := Q) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    ?_ ?_ (fun _ => rfl) ?_ hcont hres
  · intro L0 M0' G0' ⟨_,⟨H,hH,_⟩,_⟩
    refine aqgd_conseq (P := fun L M G => ∃ Nn : BitVec 64, (L.lookup (ofString "n") = some (.val (.word Nn)) ∧
        M = M0' ∧ HeapIs G (hpOf G0')) ∧ G = G0') ?_
      (fun L M G ⟨⟨Nn,hn⟩,hM,hG⟩ => ⟨Nn,⟨hn,hM,by subst hG; rw [hpOf_eq hH]; exact hH⟩,hG⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_exE (fun Nn => ?_)
    exact aqgd_conseq (allocNA_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) Nn (hpOf G0') M0' G0') (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨Nn,h⟩)
  · intro F s values callee rs _ H _ _ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    obtain ⟨y,rfl⟩ := he s x ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,⟨H,hH,le⟩,hs⟩ ⟨Nn,⟨ev,_,al,H',hH',c1,c2⟩,oh⟩ _
    subst ev
    rw [hpOf_eq hH] at al c1 ⊢
    exact ⟨hup L H lp le (by omega) al,⟨H',hH',by omega⟩,scrIs_onlyHeap oh hs⟩

#print axioms rg_alloc
end rga
def erBody : ProgHOL 64 :=
  (.decCall (ofString "bound") .one (ofString "logs_encoded_bound") [(.var .local (ofString "logs"))] (.decCall (ofString "buf") .one (ofString "alloc") [(.op .add [(.var .local (ofString "bound")),(.const 400)])] (.dec (ofString "start") .one (.op .add [(.var .local (ofString "buf")),(.const 1)]) (.dec (ofString "p") .one (.op .add [(.var .local (ofString "start")),(.const 9)]) (.dec (ofString "w") .one (.const 0) (.seq (.ite (.cmp .notEqual (.var .local (ofString "succeeded")) (.const 0)) (.seq (.storeByte (.var .local (ofString "p")) (.const 1)) (.assign .local (ofString "w") (.const 1))) (.seq (.storeByte (.var .local (ofString "p")) (.const 128)) (.assign .local (ofString "w") (.const 1)))) (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word") [(.var .local (ofString "p")),(.var .local (ofString "cumulative_gas"))]) (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.decCall (ofString "bloom") .one (ofString "alloc") [(.const 256)] (.seq (.call (some (none,none)) (ofString "logs_bloom") [(.var .local (ofString "logs")),(.var .local (ofString "bloom"))]) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_bytes") [(.var .local (ofString "p")),(.var .local (ofString "bloom")),(.const 256)]) (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "encode_logs") [(.var .local (ofString "p")),(.var .local (ofString "logs"))]) (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_finish_list") [(.var .local (ofString "start")),(.var .local (ofString "p"))]) (.seq (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0)) (.seq (.storeByte (.op .sub [(.var .local (ofString "start")),(.const 1)]) (.var .local (ofString "tx_type"))) (.return (.rstruct [(.op .sub [(.var .local (ofString "start")),(.const 1)]),(.op .add [(.var .local (ofString "w")),(.const 1)])]))) .skip) (.return (.rstruct [(.var .local (ofString "start")),(.var .local (ofString "w"))])))))))))))))))))))

theorem erBody_eq : sourceFunctionBody Guest.guestFn_encode_receipt = erBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_encode_receipt,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


/-- Parameters of `encode_receipt` are words. -/
def ERP (L : GA) : Prop :=
  (∃ a : BitVec 64, L.lookup (ofString "tx_type") = some (.val (.word a))) ∧
  (∃ b : BitVec 64, L.lookup (ofString "succeeded") = some (.val (.word b))) ∧
  (∃ c : BitVec 64, L.lookup (ofString "cumulative_gas") = some (.val (.word c))) ∧
  (∃ d : BitVec 64, L.lookup (ofString "logs") = some (.val (.word d)))

theorem erp_upd {L : GA} (h : ERP L) (x : MlS) (v : ValueHOL 64) (h1 : ofString "tx_type" ≠ x)
    (h2 : ofString "succeeded" ≠ x) (h3 : ofString "cumulative_gas" ≠ x) (h4 : ofString "logs" ≠ x) :
    ERP (L.update (x,v)) :=
  let ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩ := h
  ⟨⟨a,by rw [lookup_update_ne' _ _ h1]; exact ha⟩,⟨b,by rw [lookup_update_ne' _ _ h2]; exact hb⟩,
    ⟨c,by rw [lookup_update_ne' _ _ h3]; exact hc⟩,⟨d,by rw [lookup_update_ne' _ _ h4]; exact hd⟩⟩

section er
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat}

/-- `encode_receipt` locals: parameters, `start = X + 1`. -/
def ERCS (X : BitVec 64) (L : GA) : Prop :=
  ERP L ∧ L.lookup (ofString "start") = some (.val (.word (X + 1#64)))

/-- ... and the cursor `p = P` with `X + 10 ≤ P ≤ Bnd`. -/
def ERCP (X : BitVec 64) (Bnd : Nat) (L : GA) : Prop :=
  ERCS X L ∧ ∃ P : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧ X.toNat + 10 ≤ P.toNat ∧ P.toNat ≤ Bnd

theorem ercs_upd {X : BitVec 64} {L : GA} (h : ERCS X L) (x : MlS) (v : ValueHOL 64) (h1 : ofString "tx_type" ≠ x)
    (h2 : ofString "succeeded" ≠ x) (h3 : ofString "cumulative_gas" ≠ x) (h4 : ofString "logs" ≠ x)
    (h5 : ofString "start" ≠ x) : ERCS X (L.update (x,v)) :=
  ⟨erp_upd h.1 x v h1 h2 h3 h4,by rw [lookup_update_ne' _ _ h5]; exact h.2⟩

theorem ercp_upd {X : BitVec 64} {Bnd : Nat} {L : GA} (h : ERCP X Bnd L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "tx_type" ≠ x) (h2 : ofString "succeeded" ≠ x) (h3 : ofString "cumulative_gas" ≠ x)
    (h4 : ofString "logs" ≠ x) (h5 : ofString "start" ≠ x) (h6 : ofString "p" ≠ x) : ERCP X Bnd (L.update (x,v)) :=
  let ⟨cs,P,hp,a,b⟩ := h; ⟨ercs_upd cs x v h1 h2 h3 h4 h5,P,by rw [lookup_update_ne' _ _ h6]; exact hp,a,b⟩

theorem ercp_w {X : BitVec 64} {Bnd : Nat} (L : GA) (v : ValueHOL 64) (h : ERCP X Bnd L) :
    ERCP X Bnd (L.update (ofString "w",v)) :=
  ercp_upd h _ v (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def erT2 : ProgHOL 64 :=
  (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "encode_logs") [(.var .local (ofString "p")),(.var .local (ofString "logs"))]) (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_finish_list") [(.var .local (ofString "start")),(.var .local (ofString "p"))]) (.seq (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0)) (.seq (.storeByte (.op .sub [(.var .local (ofString "start")),(.const 1)]) (.var .local (ofString "tx_type"))) (.return (.rstruct [(.op .sub [(.var .local (ofString "start")),(.const 1)]),(.op .add [(.var .local (ofString "w")),(.const 1)])]))) .skip) (.return (.rstruct [(.var .local (ofString "start")),(.var .local (ofString "w"))]))))))

def erT1 : ProgHOL 64 :=
  (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_word") [(.var .local (ofString "p")),(.var .local (ofString "cumulative_gas"))]) (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) (.decCall (ofString "bloom") .one (ofString "alloc") [(.const 256)] (.seq (.call (some (none,none)) (ofString "logs_bloom") [(.var .local (ofString "logs")),(.var .local (ofString "bloom"))]) (.seq (.call (some ((some (.local,ofString "w")),none)) (ofString "rlp_encode_bytes") [(.var .local (ofString "p")),(.var .local (ofString "bloom")),(.const 256)]) (.seq (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) erT2))))))

section er
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat}

theorem er_kg {Lo Sc : BitVec 64} {p : ProgHOL 64} {P Q : GA → Prop} (hk : keepsGA goodGA p = true)
    (h : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ _ => P L) (fun L _ _ => Q L)
      (fun _ _ _ => True) p) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => P L ∧ RG Lo Sc G)
      (fun L _ G => Q L ∧ RG Lo Sc G) (fun _ _ G => RG Lo Sc G) p :=
  aqgd_conseq (aqgd_keepGI (GI := RG Lo Sc) hk h) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.2)

/-- `p = p + w` after a writer with `p + w ≤ B1`. -/
theorem er_adv {Lo Sc X : BitVec 64} (B0 B1 : Nat) (hB1 : B1 < 2 ^ 64) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (ERCP X B0 L ∧ ∃ Cv R : BitVec 64, L.lookup (ofString "p") = some (.val (.word Cv)) ∧
        L.lookup (ofString "w") = some (.val (.word R)) ∧ Cv.toNat + R.toNat ≤ B1) ∧ RG Lo Sc G)
      (fun L _ G => ERCP X B1 L ∧ RG Lo Sc G) (fun _ _ G => RG Lo Sc G)
      (.assign .local (ofString "p") (.op .add [(.var .local (ofString "p")),(.var .local (ofString "w"))])) :=
  aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨cs,P,hp,a,b⟩,Cv,R,hc,hw',hb⟩,rg⟩ _ ev => by
    rw [hp] at hc
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hc
    subst hc
    simp [EV,evalHOLExact,evalListHOLExact,hp,hw',wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have e : (P + R).toNat = P.toNat + R.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨⟨ercs_upd cs _ _ (by decide) (by decide) (by decide) (by decide) (by decide),P + R,lookup_update_eq' _ _ _,
      by omega,by omega⟩,rg⟩)

#print axioms er_adv

/-- `encode_receipt` from the `encode_logs` call: logs, finish list, type byte, returns. -/
theorem erT2_wn (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (Lo Sc X : BitVec 64)
    (hw : w.toNat < Lo.toNat) (hLo8 : Lo.toNat % 8 = 0) (hXl : Lo.toNat ≤ X.toNat) (hXh : X.toNat ≤ 33806089496) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => ERCP X (DF + 8) L ∧ RG Lo Sc G)
      (fun _ _ _ => False) (fun _ _ G => RG Lo Sc G) erT2 := by
  unfold erT2
  have hF9 : Fence D (DF + 9) := fence_mono hF (by omega)
  refine aqgd_seq (er_kg (by decide) (cel_call (LP := ERCP X (DF + 8)) (ofString "p") (by decide) _
    hF hDF Lo hLo8 hw (fun L ⟨_,P,hp,a,b⟩ => ⟨P,hp,by omega,b⟩) ercp_w)) ?_
  refine aqgd_seq (er_adv (DF + 8) (DF + 9 + 8) (by omega)) ?_
  refine aqgd_seq (er_kg (by decide) (fl_call (LP := ERCP X (DF + 9 + 8)) (ofString "start") (ofString "p") (by decide)
    hF9 (by omega) Lo hLo8 hw (fun L ⟨⟨_,hs⟩,P,hp,a,b⟩ => ⟨X + 1#64,P,hs,hp,by simp [BitVec.toNat_add]; omega,
      by simp [BitVec.toNat_add]; omega,b⟩) ercp_w)) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (r_stbG (LP := fun L G => (ERCP X (DF + 9 + 8) L ∧ ∃ Dv R : BitVec 64,
      L.lookup (ofString "start") = some (.val (.word Dv)) ∧ L.lookup (ofString "w") = some (.val (.word R)) ∧
      Dv.toNat + R.toNat ≤ DF + 9 + 8) ∧ RG Lo Sc G) (LQ := fun _ G => RG Lo Sc G) Lo hLo8 hw _ _
      (fun s _ ⟨⟨⟨⟨_,hs⟩,_⟩,_⟩,rg⟩ => ⟨X + 1#64 - 1#64,by simp [EV,evalHOLExact,evalListHOLExact,hs,wordOpHOL,wordOp,
        valueIsWord,valueWord],by simp; omega,fun _ => rg⟩))
    (aqgd_return _ (fun _ _ _ _ _ rg _ _ => rg))) aqgd_skip) ?_
  exact aqgd_return _ (fun _ _ _ _ _ ⟨_,rg⟩ _ _ => rg)

#print axioms erT2_wn

/-- `encode_receipt` from the `rlp_encode_word` call: gas word, bloom block, bloom bytes, then `erT2`. -/
theorem erT1_wn (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (Lo Sc K Pd X : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (hLo8 : Lo.toNat % 8 = 0) (hXl : Lo.toNat ≤ X.toNat)
    (hXh : X.toNat ≤ 33806089496) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => ERCP X (33806089496 + 11) L ∧ RG Lo Sc G) (fun _ _ _ => False) (fun _ _ G => RG Lo Sc G) erT1 := by
  unfold erT1
  have hDF0 : DF ≤ 2 ^ 62 := by omega
  refine aqgd_seq (er_kg (by decide) (cew_call (LP := ERCP X (33806089496 + 11)) (ofString "p") (by decide) _
    hF Lo hLo8 hw (fun L ⟨_,P,hp,a,b⟩ => ⟨P,hp,by omega,by omega⟩) ercp_w)) ?_
  refine aqgd_seq (er_adv (33806089496 + 11) (DF + 8) (by omega)) ?_
  refine rg_alloc (LP := ERCP X (DF + 8)) (LP' := fun L => ERCP X (DF + 8) L ∧ ∃ Bl : BitVec 64,
      L.lookup (ofString "bloom") = some (.val (.word Bl)) ∧ Lo.toNat ≤ Bl.toNat ∧ Bl.toNat ≤ 33806089496) _ _ Lo Sc
    (fun s x ev => ⟨256#64,by simp [EV,evalHOLExact] at ev; exact ev.symm⟩)
    (fun L Bl lp lo hi _ => ⟨ercp_upd lp _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),Bl,
      lookup_update_eq' _ _ _,lo,hi⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_conseq (P := fun L _ G => ∃ Bl : BitVec 64, ((ERCP X (DF + 8) L ∧
      L.lookup (ofString "bloom") = some (.val (.word Bl))) ∧ RG Lo Sc G) ∧ (Lo.toNat ≤ Bl.toNat ∧
      Bl.toNat ≤ 33806089496)) ?_ (fun _ _ _ ⟨⟨cp,Bl,hb,lo,hi⟩,rg⟩ => ⟨Bl,⟨⟨cp,hb⟩,rg⟩,lo,hi⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)
  refine aqgd_exE (fun Bl => aqgd_pureE (fun ⟨hBl,hBlh⟩ => ?_))
  let CB := fun L : GA => ERCP X (DF + 8) L ∧ L.lookup (ofString "bloom") = some (.val (.word Bl))
  -- logs_bloom(logs, bloom)
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := CB) (Rv := fun _ => True)
    (fun L => L.lookup (ofString "out") = some (.val (.word Bl))) _ _ _ _ _ originalRuntimeCode_logsBloom_lookup
    (aqgd_conseq (logsBloom_wn Lo Sc K Pd Bl hK0 hPd0 hw oK oP hLo8 hBl (by omega)) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs ⟨_,hb⟩ args lookup => by
      obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      have := evalList_nil' s _ r2; subst this
      simp [EV,evalHOLExact,hb] at ev2; subst ev2
      have e := callee_eq originalRuntimeCode_logsBloom_lookup lookup
      rw [e]; simp (config := {decide := true}))) ?_
  -- w = rlp_encode_bytes(p, bloom, 256)
  refine aqgd_seq (Q := fun L _ G => (ERCP X (DF + 8) L ∧ ∃ Cv R : BitVec 64,
      L.lookup (ofString "p") = some (.val (.word Cv)) ∧ L.lookup (ofString "w") = some (.val (.word R)) ∧
      Cv.toNat + R.toNat ≤ DF + 8) ∧ RG Lo Sc G)
    (aqgd_conseq (er_kg (by decide) (cab_call (LP := CB) (ofString "p") (by decide) _ _
    hF hDF0 Lo hLo8 hw (fun L ⟨⟨_,P,hp,a,b⟩,_⟩ => ⟨P,hp,by omega,by omega⟩)
    (fun L v h => ⟨ercp_w L v h.1,by rw [lookup_update_ne' _ _ (by decide)]; exact h.2⟩))) (fun _ _ _ h => h)
    (fun _ _ _ ⟨⟨cb,x⟩,rg⟩ => ⟨⟨cb.1,x⟩,rg⟩) (fun _ _ _ h => h)) ?_
  refine aqgd_seq (er_adv (DF + 8) (DF + 8) (by omega)) ?_
  exact erT2_wn hF hDF hcap Lo Sc X hw hLo8 hXl hXh

#print axioms erT1_wn

/-- The actual `encode_receipt(tx_type, succeeded, cumulative_gas, logs)` (watched form): every write in fresh blocks
at or above the entry heap pointer `≥ Lo` (fenced cursors) or in the Keccak windows; `RG Lo Sc` kept. -/
theorem encReceipt_wn (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (hLo8 : Lo.toNat % 8 = 0) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => ERP L ∧ RG Lo Sc G)
      (fun _ _ _ => False) (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_encode_receipt) := by
  rw [erBody_eq]; unfold erBody
  -- bound = logs_encoded_bound(logs)
  refine aqgd_decCall_mf (I' := fun L _ G => ERP L ∧ RG Lo Sc G) _ _ _ _ _ _ _
    originalRuntimeCode_logsEncodedBound_lookup (by simp)
    (memoryFrame_of_good originalRuntimeCode_logsEncodedBound_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_logs_encoded_bound) (by body_check Guest.guestFn_logs_encoded_bound)
    (fun L M G v pre => ⟨erp_upd pre.1 _ v (by decide) (by decide) (by decide) (by decide),pre.2⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  -- buf = alloc(bound + 400)
  refine rg_alloc (LP := ERP) (LP' := fun L => ERP L ∧ ∃ X : BitVec 64, L.lookup (ofString "buf") = some (.val (.word X)) ∧
      Lo.toNat ≤ X.toNat ∧ X.toNat ≤ 33806089496) _ _ Lo Sc (fun s x ev => ev_op_word s _ _ x ev)
    (fun L X lp lo hi _ => ⟨erp_upd lp _ _ (by decide) (by decide) (by decide) (by decide),X,lookup_update_eq' _ _ _,
      lo,hi⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_conseq (P := fun L _ G => ∃ X : BitVec 64, ((ERP L ∧ L.lookup (ofString "buf") = some (.val (.word X))) ∧
      RG Lo Sc G) ∧ (Lo.toNat ≤ X.toNat ∧ X.toNat ≤ 33806089496)) ?_
    (fun _ _ _ ⟨⟨ep,X,hb,lo,hi⟩,rg⟩ => ⟨X,⟨⟨ep,hb⟩,rg⟩,lo,hi⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_exE (fun X => aqgd_pureE (fun ⟨hXl,hXh⟩ => ?_))
  have e10 : (X + 1#64 + 9#64).toNat = X.toNat + 10 := by simp [BitVec.toNat_add]; omega
  -- start = buf + 1
  refine aqgd_dec (Pb := fun L _ G => ERCS X L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ ⟨⟨ep,hb⟩,rg⟩ _ ev _ => ?_) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · simp [EV,evalHOLExact,evalListHOLExact,hb,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨⟨erp_upd ep _ _ (by decide) (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,rg⟩
  -- p = start + 9
  refine aqgd_dec (Pb := fun L _ G => ERCP X (33806089496 + 10) L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False) _ _ _
    (fun h => h.elim) (fun s v _ _ _ ⟨cs,rg⟩ _ ev _ => ?_) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · simp [EV,evalHOLExact,evalListHOLExact,cs.2,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨⟨ercs_upd cs _ _ (by decide) (by decide) (by decide) (by decide) (by decide),X + 1#64 + 9#64,
      lookup_update_eq' _ _ _,by omega,by omega⟩,rg⟩
  -- w = 0
  refine aqgd_dec (Pb := fun L _ G => ERCP X (33806089496 + 10) L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False) _ _ _
    (fun h => h.elim) (fun s v _ _ _ ⟨cp,rg⟩ _ _ _ => ⟨ercp_w _ _ cp,rg⟩) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  -- status byte; w = 1
  have stp : ∀ (c : ExpHOL 64), AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => ERCP X (33806089496 + 10) L ∧ RG Lo Sc G) (fun L _ G => ERCP X (33806089496 + 10) L ∧ RG Lo Sc G)
      (fun _ _ G => RG Lo Sc G) (.storeByte (.var .local (ofString "p")) c) := fun c =>
    r_stbG (LP := fun L G => ERCP X (33806089496 + 10) L ∧ RG Lo Sc G)
      (LQ := fun L G => ERCP X (33806089496 + 10) L ∧ RG Lo Sc G)
      Lo hLo8 hw _ _ (fun s _ ⟨⟨cs,P,hp,a,b⟩,rg⟩ => ⟨P,by simp [EV,evalHOLExact,hp],by omega,fun _ => ⟨⟨cs,P,hp,a,b⟩,rg⟩⟩)
  have asw : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => ERCP X (33806089496 + 10) L ∧ RG Lo Sc G)
      (fun L _ G => (ERCP X (33806089496 + 10) L ∧ ∃ Cv R : BitVec 64, L.lookup (ofString "p") = some (.val (.word Cv)) ∧
        L.lookup (ofString "w") = some (.val (.word R)) ∧ Cv.toNat + R.toNat ≤ 33806089496 + 11) ∧ RG Lo Sc G)
      (fun _ _ G => RG Lo Sc G) (.assign .local (ofString "w") (.const 1)) :=
    aqgd_assignLocal _ _ (fun s v _ _ ⟨cp,rg⟩ _ ev => by
      simp [EV,evalHOLExact] at ev; subst ev
      obtain ⟨cs,P,hp,a,b⟩ := cp
      exact ⟨⟨ercp_w _ _ ⟨cs,P,hp,a,b⟩,P,1#64,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,
        lookup_update_eq' _ _ _,by simp; omega⟩,rg⟩)
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (stp _) asw) (aqgd_seq (stp _) asw)) ?_
  refine aqgd_seq (er_adv (33806089496 + 10) (33806089496 + 11) (by omega)) ?_
  exact erT1_wn hF hDF hcap Lo Sc K Pd X hK0 hPd0 hw oK oP hLo8 hXl hXh

#print axioms encReceipt_wn
end er
end er
end InitECandidate.Runtime
