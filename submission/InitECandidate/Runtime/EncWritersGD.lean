import InitECandidate.Runtime.EncFenceBase
import InitECandidate.Runtime.DigitsDivmodGD
/-!
Fenced window specs of the actual RLP header writers (`rlp_write_header`, `rlp_encode_word`: at most 9 bytes at `dst`,
return `dst + r ≤ DF + 8`) and of `memcpy` (writes only `[dst, dst+n)`, return `dst + n ≤ DF + 8`), under an explicit
domain fence `Fence D DF` with `DF ≤ 2^62` and an aligned lower fence `Lo` below which every word is kept.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The shared tail of `rlp_write_header` / `rlp_encode_word`: length prefix byte, big-endian length, `1 + ll`. -/
def hdrTail (xname : MlS) (e : ExpHOL 64) : ProgHOL 64 :=
  ProgHOL.decCall (ofString "ll") ShapeHOL.one (ofString "rlp_be_len") [ExpHOL.var VarKind.local xname]
    (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.var VarKind.local (ofString "dst")) e)
      (ProgHOL.seq (ProgHOL.call (some (none, none)) (ofString "rlp_put_be")
          [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.const 1#64],
            ExpHOL.var VarKind.local xname, ExpHOL.var VarKind.local (ofString "ll")])
        (ProgHOL.return (ExpHOL.op BinOp.add [ExpHOL.const 1#64, ExpHOL.var VarKind.local (ofString "ll")]))))

/-- Return of a header-style writer at `Dst`: `1 ≤ R ≤ 9` and `Dst + R ≤ DF + 8`. -/
def HdrRet (DF : Nat) (Dst : BitVec 64) (r : ValueHOL 64) : Prop :=
  ∃ R : BitVec 64, r = .val (.word R) ∧ 1 ≤ R.toNat ∧ R.toNat ≤ 9 ∧ Dst.toNat + R.toNat ≤ DF + 8

section ht
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}

theorem hdrTail_win (hF : Fence D DF) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst X : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hfit : Dst.toNat + 16 < 2 ^ 64) (xname : MlS)
    (hxl : xname ≠ ofString "ll") (hxd : ofString "dst" ≠ xname) (e : ExpHOL 64) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup xname = some (.val (.word X)))
      (fun _ _ _ => False) (fun r _ _ => HdrRet DF Dst r) (hdrTail xname e) := by
  unfold hdrTail
  let Pc := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup xname = some (.val (.word X)) ∧
    ∃ Lw : BitVec 64, L.lookup (ofString "ll") = some (.val (.word Lw)) ∧ Lw.toNat ≤ 8
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) => L.lookup (ofString "v") = some (.val (.word X)))
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) =>
      ∃ n : BitVec 64, r = .val (.word n) ∧ n.toNat ≤ 8)
    (Pc := fun L _ _ => Pc L) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_rlpBeLen_lookup (by simp)
    (fun _ _ _ _ => by
      rw [beLenBody_eq]
      exact aqgd_conseq (beLen_spec X) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ _ ⟨_,hx⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hx] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpBeLen_lookup lookup
    rw [e]; simp
  · intro L _ _ r _ _ ⟨hd,hx⟩ ⟨n,hr,hn⟩ _
    subst hr
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ hxl]; exact hx,n,
      lookup_update_eq' _ _ _,hn⟩
  refine aqgd_seq (r_stb (LP := Pc) (LQ := fun L => Pc L ∧ Dst.toNat < DF + 8) Lo hLo8 hw _ _ ?_) ?_
  · intro F s _ lp
    exact ⟨Dst,by simp [EV,evalHOLExact,lp.1],hDst,fun hD => ⟨lp,fence_byte hF hD⟩⟩
  refine aqgd_seq (Q := fun L _ _ => (Pc L ∧ Dst.toNat < DF + 8) ∧
      ((wordOf L (ofString "ll")).toNat = 0 ∨ Dst.toNat + 1 + (wordOf L (ofString "ll")).toNat ≤ DF + 8))
    (aqgd_callSpec (Vn' := fun _ => False)
      (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
        L.lookup (ofString "dst") = some (.val (.word (Dst + 1))) ∧
          L.lookup (ofString "n") = some (.val (.word (wordOf L0 (ofString "ll")))))
      (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (_ : ValueHOL 64) (_ : Mem) (_ : GA) =>
        (wordOf L0 (ofString "ll")).toNat = 0 ∨ Dst.toNat + 1 + (wordOf L0 (ofString "ll")).toNat ≤ DF + 8)
      _ _ _ _ _ originalRuntimeCode_rlpPutBe_lookup (by simp) ?_ ?_ (fun _ _ _ _ _ _ pre rre => ⟨pre,rre⟩))
    (aqgd_return _ ?_)
  · intro L0 _ _ ⟨⟨_,_,Lw,hl,hle⟩,_⟩
    rw [wordOf_eq hl,putBeBody_eq]
    have e1 : (Dst + 1).toNat = Dst.toNat + 1 := by simp [BitVec.toNat_add]; omega
    exact aqgd_conseq (putBe_win hF Lo hLo8 hw (Dst + 1) Lw (by omega) (by omega) hle) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => by rw [e1] at h; omega)
  · intro F s values callee rs _ _ _ ⟨⟨hd,hx,Lw,hl,_⟩,_⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,hx,hl,wordOpHOL,wordOp,valueIsWord,valueWord] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpPutBe_lookup lookup
    rw [wordOf_eq hl]
    refine ⟨?_,?_⟩ <;> (rw [e]; simp (config := {decide := true}))
  · intro F s v _ _ _ ⟨⟨⟨_,_,Lw,hl,hle⟩,hlt⟩,hr⟩ _ ev
    rw [wordOf_eq hl] at hr
    simp [EV,evalHOLExact,evalListHOLExact,hl,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (1 + Lw).toNat = 1 + Lw.toNat := by simp [BitVec.toNat_add]; omega
    refine ⟨1 + Lw,rfl,by omega,by omega,?_⟩
    rw [e1]; omega

#print axioms hdrTail_win
end ht
def whBody : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notLower (ExpHOL.const 55#64) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.var VarKind.local (ofString "dst")) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "base"), ExpHOL.var VarKind.local (ofString "n")])) (ProgHOL.return (ExpHOL.const 1#64))) ProgHOL.skip) (hdrTail (ofString "n") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "base"), ExpHOL.const 55#64, ExpHOL.var VarKind.local (ofString "ll")]))

def ewBody : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "w")) (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.var VarKind.local (ofString "dst")) (ExpHOL.const 128#64)) (ProgHOL.return (ExpHOL.const 1#64))) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "w")) (ExpHOL.const 128#64)) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.var VarKind.local (ofString "dst")) (ExpHOL.var VarKind.local (ofString "w"))) (ProgHOL.return (ExpHOL.const 1#64))) ProgHOL.skip) (hdrTail (ofString "w") (ExpHOL.op BinOp.add [ExpHOL.const 128#64, ExpHOL.var VarKind.local (ofString "ll")])))

theorem whBody_eq : sourceFunctionBody Guest.guestFn_rlp_write_header = whBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_write_header,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

theorem ewBody_eq : sourceFunctionBody Guest.guestFn_rlp_encode_word = ewBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_encode_word,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


section hw
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}

/-- `st8 dst, v; return 1` at `Dst`. -/
theorem oneByte_win (hF : Fence D DF) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) {LP : GA → Prop}
    (hd : ∀ L, LP L → L.lookup (ofString "dst") = some (.val (.word Dst))) (v : ExpHOL 64) {Q : GA → Mem → GA → Prop} :
    AQGD D B A w (fun _ => False) (fun L _ _ => LP L) Q (fun r _ _ => HdrRet DF Dst r)
      (.seq (.storeByte (.var .local (ofString "dst")) v) (.return (.const 1#64))) :=
  aqgd_seq (r_stb (LP := LP) (LQ := fun _ => Dst.toNat < DF + 8) Lo hLo8 hw _ _
      (fun s _ lp => ⟨Dst,by simp [EV,evalHOLExact,hd _ lp],hDst,fun hD => fence_byte hF hD⟩))
    (aqgd_return _ (fun _ v _ _ _ h _ ev => by
      simp [EV,evalHOLExact] at ev; subst ev
      exact ⟨1,rfl,by simp,by simp,by simp; omega⟩))

theorem writeHeader_win (hF : Fence D DF) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst Nn : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hfit : Dst.toNat + 16 < 2 ^ 64) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup (ofString "n") = some (.val (.word Nn)))
      (fun _ _ _ => False) (fun r _ _ => HdrRet DF Dst r) (sourceFunctionBody Guest.guestFn_rlp_write_header) := by
  rw [whBody_eq]; unfold whBody
  exact aqgd_seq (r_ite _ (oneByte_win hF Lo hLo8 hw Dst hDst (fun _ h => h.1) _) aqgd_skip)
    (hdrTail_win hF Lo hLo8 hw Dst Nn hDst hfit _ (by decide) (by decide) _)

theorem encodeWord_win (hF : Fence D DF) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst W : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hfit : Dst.toNat + 16 < 2 ^ 64) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup (ofString "w") = some (.val (.word W)))
      (fun _ _ _ => False) (fun r _ _ => HdrRet DF Dst r) (sourceFunctionBody Guest.guestFn_rlp_encode_word) := by
  rw [ewBody_eq]; unfold ewBody
  exact aqgd_seq (r_ite _ (oneByte_win hF Lo hLo8 hw Dst hDst (fun _ h => h.1) _) aqgd_skip)
    (aqgd_seq (r_ite _ (oneByte_win hF Lo hLo8 hw Dst hDst (fun _ h => h.1) _) aqgd_skip)
      (hdrTail_win hF Lo hLo8 hw Dst W hDst hfit _ (by decide) (by decide) _))

#print axioms writeHeader_win
#print axioms encodeWord_win
end hw
def mcA : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n")) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 32#64])) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")]))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]) (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 16#64]) (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 16#64]))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 24#64]) (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 24#64]))) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 32#64]))))))

def mcB : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n")) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64])) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")]))) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64])))

def mcC : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n")) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64])) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")]))) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64]) (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64]))) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 2#64]) (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 2#64]))) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 3#64]) (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 3#64]))) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 4#64]) (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 4#64]))) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 5#64]) (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 5#64]))) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 6#64]) (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 6#64]))) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 7#64]) (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 7#64]))) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]))))))))))

def mcD : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "src"), ExpHOL.var VarKind.local (ofString "i")]))) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])))

def mcBody : ProgHOL 64 :=
  ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.op BinOp.and [ExpHOL.op BinOp.or [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "src")], ExpHOL.const 7#64]) (ExpHOL.const 0#64)) (ProgHOL.seq mcA mcB) ProgHOL.skip) (ProgHOL.seq mcC (ProgHOL.seq mcD (ProgHOL.return (ExpHOL.const 0#64)))))

theorem mcBody_eq : sourceFunctionBody Guest.guestFn_memcpy = mcBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_memcpy,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- Cursor invariant of `memcpy`: `dst = Dst`, `i = I` with `Dst + I ≤ DF + 8`. -/
def McI (DF : Nat) (Dst Nn : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup (ofString "n") = some (.val (.word Nn)) ∧
    ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ Dst.toNat + I.toNat ≤ DF + 8

section mc
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop} {DF : Nat}

theorem mc_stw (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hw : w.toNat < Lo.toNat) (Dst Nn : BitVec 64)
    (hDst : Lo.toNat ≤ Dst.toNat) (j : Nat) (hj : j ≤ 24) (d v : ExpHOL 64)
    (hev : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (I : BitVec 64),
      s.locals.lookup (ofString "dst") = some (.val (.word Dst)) → s.locals.lookup (ofString "i") = some (.val (.word I)) →
      EV s d = some (.val (.word (Dst + I + BitVec.ofNat 64 j))))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, EV s v = some x → ∃ y : BitVec 64, x = .val (.word y))
    {LQ : GA → Prop}
    (hq : ∀ L, McI DF Dst Nn L → ∀ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) →
      Dst.toNat + I.toNat + j < DF → LQ L) :
    AQGD D B A w Vn (fun L _ _ => McI DF Dst Nn L) (fun L _ _ => LQ L) RR (.store d v) :=
  r_stw Lo hw d v (fun s _ ⟨hd,hn,I,hi,hb⟩ => by
      have e : (Dst + I + BitVec.ofNat 64 j).toNat = Dst.toNat + I.toNat + j := by
        simp [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
      exact ⟨_,hev s I hd hi,by omega,fun hD => hq _ ⟨hd,hn,I,hi,hb⟩ I hi (by have := hF _ hD; omega)⟩)
    (fun s x _ _ _ ev => hv s x ev)

theorem mc_stb (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dst Nn : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (j : Nat) (hj : j ≤ 7) (d v : ExpHOL 64)
    (hev : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (I : BitVec 64),
      s.locals.lookup (ofString "dst") = some (.val (.word Dst)) → s.locals.lookup (ofString "i") = some (.val (.word I)) →
      EV s d = some (.val (.word (Dst + I + BitVec.ofNat 64 j))))
    {LQ : GA → Prop}
    (hq : ∀ L, McI DF Dst Nn L → ∀ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) →
      Dst.toNat + I.toNat + j < DF + 8 → LQ L) :
    AQGD D B A w Vn (fun L _ _ => McI DF Dst Nn L) (fun L _ _ => LQ L) RR (.storeByte d v) :=
  r_stb Lo hLo8 hw d v (fun s _ ⟨hd,hn,I,hi,hb⟩ => by
      have e : (Dst + I + BitVec.ofNat 64 j).toNat = Dst.toNat + I.toNat + j := by
        simp [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
      exact ⟨_,hev s I hd hi,by omega,fun hD => hq _ ⟨hd,hn,I,hi,hb⟩ I hi (by have := fence_byte hF hD; omega)⟩)

/-- Advancing the `memcpy` cursor by `k` once `Dst + I + k ≤ DF + 8` is known. -/
theorem mc_adv (hDF : DF ≤ 2 ^ 62) (Dst Nn : BitVec 64) (k : Nat) (hk : k ≤ 32) :
    AQGD D B A w Vn (fun L _ _ => McI DF Dst Nn L ∧ ∀ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) →
        Dst.toNat + I.toNat + k ≤ DF + 8)
      (fun L _ _ => McI DF Dst Nn L) RR
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const (BitVec.ofNat 64 k)])) :=
  r_assign _ _ (fun s v _ ⟨⟨hd,hn,I,hi,hb⟩,hk'⟩ ev => by
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have h2 := hk' I hi
    have e : (I + BitVec.ofNat 64 k).toNat = I.toNat + k := by
      simp [BitVec.toNat_add,BitVec.toNat_ofNat]; have := Dst.isLt; omega
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hn,_,
      lookup_update_eq' _ _ _,by rw [e]; omega⟩)

theorem mcA_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst Nn : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) :
    AQGD D B A w Vn (fun L _ _ => McI DF Dst Nn L) (fun L _ _ => McI DF Dst Nn L) RR mcA := by
  unfold mcA
  refine r_while (LC := fun _ => True) _ (fun _ _ _ _ _ _ => trivial)
    (aqgd_conseq (P := fun L _ _ => McI DF Dst Nn L) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
  refine aqgd_seq (mc_stw (LQ := McI DF Dst Nn) hF hDF Lo hw Dst Nn hDst 0 (by decide) _ _ (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc])
    (fun s x ev => ev_load_one_word s _ x ev) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stw (LQ := McI DF Dst Nn) hF hDF Lo hw Dst Nn hDst 8 (by decide) _ _ (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc])
    (fun s x ev => ev_load_one_word s _ x ev) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stw (LQ := McI DF Dst Nn) hF hDF Lo hw Dst Nn hDst 16 (by decide) _ _ (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc])
    (fun s x ev => ev_load_one_word s _ x ev) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stw (LQ := fun L => McI DF Dst Nn L ∧ ∀ I : BitVec 64,
      L.lookup (ofString "i") = some (.val (.word I)) → Dst.toNat + I.toNat + 32 ≤ DF + 8)
    hF hDF Lo hw Dst Nn hDst 24 (by decide) _ _ (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc])
    (fun s x ev => ev_load_one_word s _ x ev)
    (fun L lp I hi hb => ⟨lp,fun I' hi' => by rw [hi] at hi'; simp at hi'; subst hi'; omega⟩)) ?_
  exact mc_adv hDF Dst Nn 32 (by decide)

#print axioms mcA_win
theorem mcB_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst Nn : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) :
    AQGD D B A w Vn (fun L _ _ => McI DF Dst Nn L) (fun L _ _ => McI DF Dst Nn L) RR mcB := by
  unfold mcB
  refine r_while (LC := fun _ => True) _ (fun _ _ _ _ _ _ => trivial)
    (aqgd_conseq (P := fun L _ _ => McI DF Dst Nn L) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
  refine aqgd_seq (mc_stw (LQ := fun L => McI DF Dst Nn L ∧ ∀ I : BitVec 64,
      L.lookup (ofString "i") = some (.val (.word I)) → Dst.toNat + I.toNat + 8 ≤ DF + 8)
    hF hDF Lo hw Dst Nn hDst 0 (by decide) _ _ (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc])
    (fun s x ev => ev_load_one_word s _ x ev)
    (fun L lp I hi hb => ⟨lp,fun I' hi' => by rw [hi] at hi'; simp at hi'; subst hi'; omega⟩)) ?_
  exact mc_adv hDF Dst Nn 8 (by decide)

#print axioms mcB_win
theorem mcC_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst Nn : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) :
    AQGD D B A w Vn (fun L _ _ => McI DF Dst Nn L) (fun L _ _ => McI DF Dst Nn L) RR mcC := by
  unfold mcC
  refine r_while (LC := fun _ => True) _ (fun _ _ _ _ _ _ => trivial)
    (aqgd_conseq (P := fun L _ _ => McI DF Dst Nn L) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
  refine aqgd_seq (mc_stb (LQ := McI DF Dst Nn) hF hDF Lo hLo8 hw Dst Nn hDst 0 (by decide) _ _
    (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stb (LQ := McI DF Dst Nn) hF hDF Lo hLo8 hw Dst Nn hDst 1 (by decide) _ _
    (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stb (LQ := McI DF Dst Nn) hF hDF Lo hLo8 hw Dst Nn hDst 2 (by decide) _ _
    (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stb (LQ := McI DF Dst Nn) hF hDF Lo hLo8 hw Dst Nn hDst 3 (by decide) _ _
    (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stb (LQ := McI DF Dst Nn) hF hDF Lo hLo8 hw Dst Nn hDst 4 (by decide) _ _
    (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stb (LQ := McI DF Dst Nn) hF hDF Lo hLo8 hw Dst Nn hDst 5 (by decide) _ _
    (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stb (LQ := McI DF Dst Nn) hF hDF Lo hLo8 hw Dst Nn hDst 6 (by decide) _ _
    (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]) (fun L lp _ _ _ => lp)) ?_
  refine aqgd_seq (mc_stb (LQ := fun L => McI DF Dst Nn L ∧ ∀ I : BitVec 64,
      L.lookup (ofString "i") = some (.val (.word I)) → Dst.toNat + I.toNat + 8 ≤ DF + 8)
    hF hDF Lo hLo8 hw Dst Nn hDst 7 (by decide) _ _ (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc])
    (fun L lp I hi hb => ⟨lp,fun I' hi' => by rw [hi] at hi'; simp at hi'; subst hi'; omega⟩)) ?_
  exact mc_adv hDF Dst Nn 8 (by decide)

#print axioms mcC_win

theorem mcD_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst Nn : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) :
    AQGD D B A w Vn (fun L _ _ => McI DF Dst Nn L)
      (fun L _ _ => McI DF Dst Nn L ∧ ∀ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) →
        Nn.toNat ≤ I.toNat) RR mcD := by
  unfold mcD
  refine aqgd_conseq (aqgd_whileE (I := fun L _ _ => McI DF Dst Nn L) (C := fun _ _ _ => True)
    (E := fun L _ _ => ∀ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) → Nn.toNat ≤ I.toNat)
    (Qb := fun _ _ _ => False) _ (fun _ _ _ _ _ _ _ _ => trivial) ?_ (aqgb_of_aqgd ?_))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h)
  · intro F s x _ _ ⟨_,hn,I,hi,_⟩ _ ev z I' hi'
    rw [hi] at hi'; simp at hi'; subst hi'
    simp [EV,evalHOLExact,hi,hn,Compiler.Encoders.Asm.wordCmpHOL] at ev
    by_cases h : I < Nn
    · simp [h] at ev; subst z; exact absurd ev (by decide)
    · simp [BitVec.lt_def] at h; omega
  refine aqgd_conseq (P := fun L _ _ => McI DF Dst Nn L) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_seq (mc_stb (LQ := fun L => McI DF Dst Nn L ∧ ∀ I : BitVec 64,
      L.lookup (ofString "i") = some (.val (.word I)) → Dst.toNat + I.toNat + 1 ≤ DF + 8)
    hF hDF Lo hLo8 hw Dst Nn hDst 0 (by decide) _ _ (fun s I hd hi => by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc])
    (fun L lp I hi hb => ⟨lp,fun I' hi' => by rw [hi] at hi'; simp at hi'; subst hi'; omega⟩)) ?_
  exact mc_adv hDF Dst Nn 1 (by decide)

#print axioms mcD_win

/-- The actual `memcpy(dst, src, n)` writes only `[dst, dst + n)` and, on return, `dst + n ≤ DF + 8`. -/
theorem memcpy_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dst Nn : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hDF8 : Dst.toNat ≤ DF + 8) :
    AQGD D B A w Vn (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "n") = some (.val (.word Nn)))
      (fun _ _ _ => False) (fun _ _ _ => Dst.toNat + Nn.toNat ≤ DF + 8) (sourceFunctionBody Guest.guestFn_memcpy) := by
  rw [mcBody_eq]; unfold mcBody
  refine r_dec (LB := McI DF Dst Nn) (LQ' := fun _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ ⟨hd,hn⟩ ev
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hn,
      0,lookup_update_eq' _ _ _,by simp; omega⟩
  refine aqgd_seq (r_ite _ (aqgd_seq (mcA_win hF hDF Lo hLo8 hw Dst Nn hDst) (mcB_win hF hDF Lo hLo8 hw Dst Nn hDst))
    aqgd_skip) (aqgd_seq (mcC_win hF hDF Lo hLo8 hw Dst Nn hDst)
      (aqgd_seq (mcD_win hF hDF Lo hLo8 hw Dst Nn hDst) (aqgd_return _ ?_)))
  intro F s v _ _ _ ⟨⟨_,_,I,hi,hb⟩,he⟩ _ _
  have := he I hi
  omega

#print axioms memcpy_win

#print axioms mc_stw
#print axioms mc_stb
#print axioms mc_adv
end mc
end InitECandidate.Runtime
