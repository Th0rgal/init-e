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
end InitECandidate.Runtime
