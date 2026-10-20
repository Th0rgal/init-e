import InitECandidate.Runtime.EncWritersGD
/-!
Fenced window specs of the actual `rlp_encode_bytes` (header plus `memcpy`), `rlp_encode_list_header` and `tx_put_to`,
with a tail-call rule against a callee spec. Every return gives a count `R` with `dst + R ≤ DF + 8`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Return of a writer at `Dst`: a word `R` with `Dst + R ≤ DF + 8`. -/
def WRet (DF : Nat) (Dst : BitVec 64) (r : ValueHOL 64) : Prop :=
  ∃ R : BitVec 64, r = .val (.word R) ∧ Dst.toNat + R.toNat ≤ DF + 8

theorem wret_of_hdr {DF : Nat} {Dst : BitVec 64} {r : ValueHOL 64} (h : HdrRet DF Dst r) : WRet DF Dst r :=
  let ⟨R,e,_,_,b⟩ := h; ⟨R,e,b⟩

def ebBody : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "n")) (ExpHOL.const 1#64)) (ProgHOL.dec (ofString "b") ShapeHOL.one (ExpHOL.loadByte (ExpHOL.var VarKind.local (ofString "src"))) (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "b")) (ExpHOL.const 128#64)) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.var VarKind.local (ofString "dst")) (ExpHOL.var VarKind.local (ofString "b"))) (ProgHOL.return (ExpHOL.const 1#64))) ProgHOL.skip)) ProgHOL.skip) (ProgHOL.decCall (ofString "h") ShapeHOL.one (ofString "rlp_write_header") [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.const 128#64, ExpHOL.var VarKind.local (ofString "n")] (ProgHOL.seq (ProgHOL.call (some (none, none)) (ofString "memcpy") [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "h")], ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "n")]) (ProgHOL.return (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "h"), ExpHOL.var VarKind.local (ofString "n")]))))

theorem ebBody_eq : sourceFunctionBody Guest.guestFn_rlp_encode_bytes = ebBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_encode_bytes,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


section eb
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}

/-- The actual `rlp_encode_bytes(dst, src, n)`: writes only at or above `dst`, returns `R` with `dst + R ≤ DF + 8`. -/
theorem encodeBytes_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dst Nn : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hfit : Dst.toNat + 16 < 2 ^ 64) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup (ofString "n") = some (.val (.word Nn)))
      (fun _ _ _ => False) (fun r _ _ => WRet DF Dst r) (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) := by
  rw [ebBody_eq]; unfold ebBody
  let P0 := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
    L.lookup (ofString "n") = some (.val (.word Nn))
  refine aqgd_seq (r_ite (LP := P0) _ (r_dec (LB := P0) (LQ' := P0) _ _ _ (fun _ => rfl)
      (fun s v _ ⟨hd,hn⟩ _ => ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hn⟩)
      (r_ite _ (aqgd_conseq (oneByte_win hF Lo hLo8 hw Dst hDst (fun _ h => h.1) _) (fun _ _ _ h => h)
        (fun _ _ _ h => h) (fun _ _ _ h => wret_of_hdr h)) aqgd_skip)
      (fun _ L' _ ⟨hd,hn⟩ => ⟨by rw [resVarEq_lookup_ne' _ _ _ _ (by decide)]; exact hd,
        by rw [resVarEq_lookup_ne' _ _ _ _ (by decide)]; exact hn⟩)) aqgd_skip) ?_
  let Pc := fun L : GA => P0 L ∧ ∃ Hw : BitVec 64, L.lookup (ofString "h") = some (.val (.word Hw)) ∧
    Hw.toNat ≤ 9 ∧ Dst.toNat + Hw.toNat ≤ DF + 8
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup (ofString "n") = some (.val (.word Nn)))
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) => HdrRet DF Dst r)
    (Pc := fun L _ _ => Pc L) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_rlpWriteHeader_lookup (by simp)
    (fun _ _ _ _ => aqgd_conseq (writeHeader_win hF Lo hLo8 hw Dst Nn hDst hfit) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ _ ⟨hd,hn⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,hn] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpWriteHeader_lookup lookup
    refine ⟨?_,?_⟩ <;> (rw [e]; simp (config := {decide := true}))
  · intro L _ _ r _ _ ⟨hd,hn⟩ ⟨Hw,hr,_,h9,hb⟩ _
    subst hr
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hn⟩,
      Hw,lookup_update_eq' _ _ _,h9,hb⟩
  refine aqgd_seq (Q := fun L _ _ => Pc L ∧ Dst.toNat + (wordOf L (ofString "h")).toNat + Nn.toNat ≤ DF + 8)
    (aqgd_callSpec (Vn' := fun _ => False)
      (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
        L.lookup (ofString "dst") = some (.val (.word (Dst + wordOf L0 (ofString "h")))) ∧
          L.lookup (ofString "n") = some (.val (.word Nn)))
      (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (_ : ValueHOL 64) (_ : Mem) (_ : GA) =>
        Dst.toNat + (wordOf L0 (ofString "h")).toNat + Nn.toNat ≤ DF + 8)
      _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ (fun _ _ _ _ _ _ pre rre => ⟨pre,rre⟩))
    (aqgd_return _ ?_)
  · intro L0 _ _ ⟨_,Hw,hh,h9,hb⟩
    rw [wordOf_eq hh]
    have e1 : (Dst + Hw).toNat = Dst.toNat + Hw.toNat := by simp [BitVec.toNat_add]; omega
    exact aqgd_conseq (memcpy_win hF hDF Lo hLo8 hw (Dst + Hw) Nn (by omega) (by omega)) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => by rw [e1] at h; omega)
  · intro F s values callee rs _ _ _ ⟨⟨hd,hn⟩,Hw,hh,_⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,hn,hh,wordOpHOL,wordOp,valueIsWord,valueWord] at args
    cases hs : s.locals.lookup (ofString "src") with
    | none => simp [hs] at args
    | some sv =>
    simp [hs] at args
    subst args
    have e := callee_eq originalRuntimeCode_memcpy_lookup lookup
    rw [wordOf_eq hh]
    refine ⟨?_,?_⟩ <;> (rw [e]; simp (config := {decide := true}))
  · intro F s v _ _ _ ⟨⟨⟨_,hn⟩,Hw,hh,_,_⟩,hb⟩ _ ev
    rw [wordOf_eq hh] at hb
    simp [EV,evalHOLExact,evalListHOLExact,hh,hn,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (Hw + Nn).toNat = Hw.toNat + Nn.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨Hw + Nn,rfl,by rw [e1]; omega⟩

#print axioms encodeBytes_win
end eb
section tcs
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A tail call against a callee spec: the callee's returns are the caller's returns. -/
theorem aqgd_tailCallSpecS {P Q : GA → Mem → GA → Prop} {Vn' : MlS → Prop}
    (Pe : GA → Mem → GA → GA → Mem → GA → Prop) (RRe : GA → Mem → GA → ValueHOL 64 → Mem → GA → Prop)
    (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hsl : ∀ values callee rs, lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      SL Vn' callee)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQGD D B A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hr : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → RR v M' H') :
    AQGD D B A w Vn P Q RR (.call none function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  split
  · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;> simp_all [Continuing]
  · rename_i values args
    split
    · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;> simp_all [Continuing]
    · rename_i found callee foundShape lookup
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      split
      · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;> simp_all [Continuing]
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (hsl values callee foundShape lookup') H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals (try split)
          all_goals first
            | (obtain ⟨H',hH',rr⟩ := r1 _ rfl
               exact ⟨by simpa [emptyLocalsHOLFinite] using m1,fun _ => by simpa [emptyLocalsHOLFinite] using a1 (by simp [Continuing]),
                (fun e => by cases e),fun v' e => by
                  simp at e; subst e
                  exact ⟨H',by unfold GIs at hH' ⊢; simpa [emptyLocalsHOLFinite] using hH',
                    by simpa [emptyLocalsHOLFinite] using hr _ _ _ _ _ _ pre rr⟩,by simp,by simp⟩)
            | (refine ⟨by simpa [emptyLocalsHOLFinite] using m1,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;>
                simp_all [Continuing])
            | (refine ⟨m1,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;> simp_all [Continuing])

#print axioms aqgd_tailCallSpecS
end tcs
def lhBody : ProgHOL 64 :=
  ProgHOL.call none (ofString "rlp_write_header") [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.const 192#64, ExpHOL.var VarKind.local (ofString "payload_len")]

def ptBody : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "to")) (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.var VarKind.local (ofString "dst")) (ExpHOL.const 128#64)) (ProgHOL.return (ExpHOL.const 1#64))) ProgHOL.skip) (ProgHOL.call none (ofString "rlp_encode_bytes") [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "to"), ExpHOL.const 20#64])

theorem lhBody_eq : sourceFunctionBody Guest.guestFn_rlp_encode_list_header = lhBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_encode_list_header,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

theorem ptBody_eq : sourceFunctionBody Guest.guestFn_tx_put_to = ptBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_tx_put_to,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


section lt
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}

theorem listHeader_win (hF : Fence D DF) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst PL : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hfit : Dst.toNat + 16 < 2 ^ 64) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "payload_len") = some (.val (.word PL)))
      (fun _ _ _ => False) (fun r _ _ => HdrRet DF Dst r) (sourceFunctionBody Guest.guestFn_rlp_encode_list_header) := by
  rw [lhBody_eq]; unfold lhBody
  exact aqgd_tailCallSpecS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
      L.lookup (ofString "n") = some (.val (.word PL)))
    (RRe := fun _ _ _ r _ _ => HdrRet DF Dst r) _ _ _ _ _ originalRuntimeCode_rlpWriteHeader_lookup
    (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ => aqgd_conseq (writeHeader_win hF Lo hLo8 hw Dst PL hDst hfit) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    (fun s values callee rs _ _ _ ⟨hd,hp⟩ _ args lookup => by
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hd,hp] at args
      subst args
      have e := callee_eq originalRuntimeCode_rlpWriteHeader_lookup lookup
      refine ⟨?_,?_⟩ <;> (rw [e]; simp (config := {decide := true})))
    (fun _ _ _ _ _ _ _ h => h)

theorem putTo_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dst : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hfit : Dst.toNat + 16 < 2 ^ 64) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)))
      (fun _ _ _ => False) (fun r _ _ => WRet DF Dst r) (sourceFunctionBody Guest.guestFn_tx_put_to) := by
  rw [ptBody_eq]; unfold ptBody
  refine aqgd_seq (r_ite (LQ := fun L => L.lookup (ofString "dst") = some (.val (.word Dst))) _
    (aqgd_conseq (oneByte_win hF Lo hLo8 hw Dst hDst (fun _ h => h) _) (fun _ _ _ h => h)
    (fun _ _ _ h => h) (fun _ _ _ h => wret_of_hdr h)) aqgd_skip) ?_
  exact aqgd_tailCallSpecS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
      L.lookup (ofString "n") = some (.val (.word 20#64)))
    (RRe := fun _ _ _ r _ _ => WRet DF Dst r) _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup
    (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ => aqgd_conseq (encodeBytes_win hF hDF Lo hLo8 hw Dst 20#64 hDst hfit) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    (fun s values callee rs _ _ _ hd _ args lookup => by
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hd] at args
      cases ht : s.locals.lookup (ofString "to") with
      | none => simp [ht] at args
      | some tv =>
      simp [ht] at args
      subst args
      have e := callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
      refine ⟨?_,?_⟩ <;> (rw [e]; simp (config := {decide := true})))
    (fun _ _ _ _ _ _ _ h => h)

#print axioms listHeader_win
#print axioms putTo_win
end lt
end InitECandidate.Runtime
