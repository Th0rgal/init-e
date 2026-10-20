import InitECandidate.Runtime.EncGenPrepGD
/-!
Fenced window spec of the actual `tx_encode_generic`: `alloc` returns the entry heap pointer `H0`, the field
writers advance a cursor from `H0 + 10` within the fence `DF + 8` (writer specs instantiated at `DF + 8`), the
mode-2 bytes, the backward list header at `H0 + 10 - hl` (`hl ≤ 9`) and the type byte stay at or above `H0`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def encTail : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "mode")) (ExpHOL.const 2#64)) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "chain_id")]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.const 128#64)) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 1#64]) (ExpHOL.const 128#64)) (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 2#64])))))) ProgHOL.skip) (ProgHOL.dec (ofString "payload_len") ShapeHOL.one (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "body")]) (ProgHOL.decCall (ofString "hl") ShapeHOL.one (ofString "rlp_list_header_len") [ExpHOL.var VarKind.local (ofString "payload_len")] (ProgHOL.dec (ofString "start") ShapeHOL.one (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "body"), ExpHOL.var VarKind.local (ofString "hl")]) (ProgHOL.seq (ProgHOL.call (some (none, none)) (ofString "rlp_encode_list_header") [ExpHOL.var VarKind.local (ofString "start"), ExpHOL.var VarKind.local (ofString "payload_len")]) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "t")) (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "start") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "start"), ExpHOL.const 1#64])) (ProgHOL.storeByte (ExpHOL.var VarKind.local (ofString "start")) (ExpHOL.var VarKind.local (ofString "t")))) ProgHOL.skip) (ProgHOL.return (ExpHOL.rstruct [ExpHOL.var VarKind.local (ofString "start"), ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "start")]])))))))

def encMid (K : ProgHOL 64) : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "t")) (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 8#64])]) (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))) ProgHOL.skip) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 16#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notLower (ExpHOL.const 1#64) (ExpHOL.var VarKind.local (ofString "t"))) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 48#64])]) (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 80#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 112#64])]) (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])))))) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 144#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_to") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 152#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 160#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 192#64]), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 200#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "t")) (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_access_list") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 208#64]), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 216#64])]) (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "t")) (ExpHOL.const 3#64)) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 224#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_blob_hashes") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 256#64]), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 264#64])]) (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))))) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "t")) (ExpHOL.const 4#64)) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_authorizations") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 272#64]), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 280#64])]) (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "mode")) (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 288#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 320#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 352#64])]) (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))))))) ProgHOL.skip) K)))))))))))))))

def geBody : ProgHOL 64 :=
  ProgHOL.decCall (ofString "bound") ShapeHOL.one (ofString "tx_encode_bound") [ExpHOL.var VarKind.local (ofString "tx")] (ProgHOL.decCall (ofString "buf") ShapeHOL.one (ofString "alloc") [ExpHOL.var VarKind.local (ofString "bound")] (ProgHOL.dec (ofString "body") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "buf"), ExpHOL.const 10#64]) (ProgHOL.dec (ofString "p") ShapeHOL.one (ExpHOL.var VarKind.local (ofString "body")) (ProgHOL.dec (ofString "t") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 0#64])) (ProgHOL.dec (ofString "w") ShapeHOL.one (ExpHOL.const 0#64) (encMid encTail))))))

theorem geBody_eq : sourceFunctionBody Guest.guestFn_tx_encode_generic = geBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_tx_encode_generic,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

section it
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

theorem aqgd_iteT {P Q : GA → Mem → GA → Prop} (c : ExpHOL 64) {y n : ProgHOL 64}
    (hy : AQGD D B A w Vn P Q RR y) (hn : AQGD D B A w Vn P Q RR n) : AQGD D B A w Vn P Q RR (.ite c y n) :=
  aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) c (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aqgd_conseq hy (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    (aqgd_conseq hn (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))

/-- `r_stb` with locals-and-globals assertions. -/
theorem r_stbG {LP LQ : GA → GA → Prop} (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → LP s.locals s.globals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ Lo.toNat ≤ a.toNat ∧
        (D (panByteAlignHOL a) → LQ s.locals s.globals)) :
    AQGD D B A w Vn (fun L _ G => LP L G) (fun L _ G => LQ L G) RR (.storeByte d v) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  obtain ⟨a,ha,hlo,hq⟩ := hd s aw pre
  have ne : w ≠ panByteAlignHOL a := by
    intro e; have := align_toNat a; rw [← e] at this; omega
  obtain ⟨res,_,loc,glob,_,_,_⟩ := evaluate_storeByte_control_frame s d v
  refine ⟨evaluate_storeByte_memory_frame s d v a w ha ne,fun _ => by rw [glob]; exact aw,
    fun e => ⟨by rw [loc]; exact sl,_,by rw [glob]; rfl,by
      rw [loc]; exact hq (dom.2.1 ▸ storeByte_none_dom' s d v a ha e)⟩,?_,?_,?_⟩
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp

#print axioms r_stbG
end it

section gm
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {DF : Nat} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {RR : ValueHOL 64 → Mem → GA → Prop}

theorem ld1 {F : Type} (s : PanSemStateFiniteExact 64 F) (a : ExpHOL 64) :
    ∀ v, EV s (.load .one a) = some v → ∃ y : BitVec 64, v = .val (.word y) := fun v ev => ev_load_one_word s _ v ev

/-- The middle of the actual `tx_encode_generic`: the field writers advance the cursor within `[Dst, DF + 8]`. -/
theorem encMid_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (Lo : BitVec 64)
    (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (H0 : BitVec 64) (hLoH : Lo.toNat ≤ H0.toNat)
    (Dst : BitVec 64) (hLD : Lo.toNat ≤ Dst.toNat) {base : GA → Prop}
    (hbw : ∀ L v, base L → base (L.update (ofString "w",v))) (hbp : ∀ L v, base L → base (L.update (ofString "p",v)))
    {K : ProgHOL 64} {Q : GA → Mem → GA → Prop}
    (hK : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => CIG DF base (HGe H0) Dst L G)
      Q RR K) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => CIG DF base (HGe H0) Dst L G)
      Q RR (encMid K) := by
  unfold encMid
  have adv := csg_adv (D := D) (B := B) (A := JWSN SP0 P0 FM G0 J C SKB Nj) (w := w) (RR := RR) (GI := HGe H0)
    hDF Dst hbp
  have cW : ∀ e2 : ExpHOL 64, (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s e2 = some v →
      ∃ y : BitVec 64, v = .val (.word y)) →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => CIG DF base (HGe H0) Dst L G)
        (fun L _ G => CIGW DF base (HGe H0) Dst L G) RR
        (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_word") [.var .local (ofString "p"),e2]) :=
    fun e2 he2 => csg_call Dst hbw _ _ _ _ _ originalRuntimeCode_rlpEncodeWord_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "w") = some (.val (.word Y)))
      (fun P h1 h2 => cs_word hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe2 originalRuntimeCode_rlpEncodeWord_lookup (by decide)
        s _ P hp (he2 s) args lookup)
  have cU : ∀ e2 : ExpHOL 64,
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => CIG DF base (HGe H0) Dst L G)
        (fun L _ G => CIGW DF base (HGe H0) Dst L G) RR
        (.call (some (some (.local,ofString "w"),none)) (ofString "tx_put_u256") [.var .local (ofString "p"),e2]) :=
    fun e2 => csg_callS Dst hbw _ _ _ _ _ originalRuntimeCode_txPutU256_lookup
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)))
      (fun P h1 h2 => cs_u256E hF hDF hcap Lo hLo8 hw H0 hLoH P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpeU s _ P hp args lookup)
  have cT : ∀ e2 : ExpHOL 64, (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s e2 = some v →
      ∃ y : BitVec 64, v = .val (.word y)) →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => CIG DF base (HGe H0) Dst L G)
        (fun L _ G => CIGW DF base (HGe H0) Dst L G) RR
        (.call (some (some (.local,ofString "w"),none)) (ofString "tx_put_to") [.var .local (ofString "p"),e2]) :=
    fun e2 he2 => csg_call Dst hbw _ _ _ _ _ originalRuntimeCode_txPutTo_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "to") = some (.val (.word Y)))
      (fun P h1 h2 => cs_to hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe2 originalRuntimeCode_txPutTo_lookup (by decide)
        s _ P hp (he2 s) args lookup)
  have cB : ∀ e2 e3 : ExpHOL 64, (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s e3 = some v →
      ∃ y : BitVec 64, v = .val (.word y)) →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => CIG DF base (HGe H0) Dst L G)
        (fun L _ G => CIGW DF base (HGe H0) Dst L G) RR
        (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes") [.var .local (ofString "p"),e2,e3]) :=
    fun e2 e3 he3 => csg_call Dst hbw _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y)))
      (fun P h1 h2 => cs_bytes hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe3 s _ _ P hp (he3 s) args lookup)
  have cAL : ∀ e2 e3 : ExpHOL 64,
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s e2 = some v → ∃ y : BitVec 64, v = .val (.word y)) →
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s e3 = some v → ∃ y : BitVec 64, v = .val (.word y)) →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => CIG DF base (HGe H0) Dst L G)
        (fun L _ G => CIGW DF base (HGe H0) Dst L G) RR
        (.call (some (some (.local,ofString "w"),none)) (ofString "tx_put_access_list") [.var .local (ofString "p"),e2,e3]) :=
    fun e2 e3 he2 he3 => csg_call Dst hbw _ _ _ _ _ originalRuntimeCode_txPutAccessList_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        (∃ Y : BitVec 64, L.lookup (ofString "recs") = some (.val (.word Y))) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y)))
      (fun P h1 h2 => cs_al hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe3g originalRuntimeCode_txPutAccessList_lookup (by decide)
        (by decide) (by decide) s _ _ P hp (he2 s) (he3 s) args lookup)
  have cBH : ∀ e2 e3 : ExpHOL 64,
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s e2 = some v → ∃ y : BitVec 64, v = .val (.word y)) →
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s e3 = some v → ∃ y : BitVec 64, v = .val (.word y)) →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => CIG DF base (HGe H0) Dst L G)
        (fun L _ G => CIGW DF base (HGe H0) Dst L G) RR
        (.call (some (some (.local,ofString "w"),none)) (ofString "tx_put_blob_hashes") [.var .local (ofString "p"),e2,e3]) :=
    fun e2 e3 he2 he3 => csg_call Dst hbw _ _ _ _ _ originalRuntimeCode_txPutBlobHashes_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        (∃ Y : BitVec 64, L.lookup (ofString "buf") = some (.val (.word Y))) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y)))
      (fun P h1 h2 => cs_bh hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => hpe3g originalRuntimeCode_txPutBlobHashes_lookup (by decide)
        (by decide) (by decide) s _ _ P hp (he2 s) (he3 s) args lookup)
  have cAU : ∀ e2 e3 : ExpHOL 64,
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s e2 = some v → ∃ y : BitVec 64, v = .val (.word y)) →
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s e3 = some v → ∃ y : BitVec 64, v = .val (.word y)) →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => CIG DF base (HGe H0) Dst L G)
        (fun L _ G => CIGW DF base (HGe H0) Dst L G) RR
        (.call (some (some (.local,ofString "w"),none)) (ofString "tx_put_authorizations") [.var .local (ofString "p"),e2,e3]) :=
    fun e2 e3 he2 he3 => csg_call Dst hbw _ _ _ _ _ originalRuntimeCode_txPutAuthorizations_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)))
      (fun P h1 h2 => cs_auE hF hDF hcap Lo hLo8 hw H0 hLoH P (by omega) h2)
      (fun s values callee rs P _ hp args lookup => (hpe3g originalRuntimeCode_txPutAuthorizations_lookup (by decide)
        (by decide) (by decide) s _ _ P hp (he2 s) (he3 s) args lookup).1)
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (cW _ (ld1 · _)) adv) aqgd_skip) ?_
  refine aqgd_seq (cU _) (aqgd_seq adv ?_)
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (cU _) adv) (aqgd_seq (cU _) (aqgd_seq adv (aqgd_seq (cU _) adv)))) ?_
  refine aqgd_seq (cW _ (ld1 · _)) (aqgd_seq adv ?_)
  refine aqgd_seq (cT _ (ld1 · _)) (aqgd_seq adv ?_)
  refine aqgd_seq (cU _) (aqgd_seq adv ?_)
  refine aqgd_seq (cB _ _ (ld1 · _)) (aqgd_seq adv ?_)
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (cAL _ _ (ld1 · _) (ld1 · _)) adv) aqgd_skip) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (cU _) (aqgd_seq adv (aqgd_seq (cBH _ _ (ld1 · _) (ld1 · _)) adv)))
    aqgd_skip) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (cAU _ _ (ld1 · _) (ld1 · _)) adv) aqgd_skip) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (cU _) (aqgd_seq adv (aqgd_seq (cU _) (aqgd_seq adv (aqgd_seq (cU _) adv)))))
    aqgd_skip) hK

#print axioms encMid_win
end gm
/-- Locals of the cursor phase of `tx_encode_generic`: `body = Dst` and a word `chain_id`. -/
def GBase (Dst : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "body") = some (.val (.word Dst)) ∧
    ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))

theorem gbase_upd {Dst : BitVec 64} (n : MlS) (h1 : ofString "body" ≠ n) (h2 : ofString "chain_id" ≠ n) (L : GA)
    (v : ValueHOL 64) (h : GBase Dst L) : GBase Dst (L.update (n,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,let ⟨c,hc⟩ := h.2; ⟨c,by rw [lookup_update_ne' _ _ h2]; exact hc⟩⟩

/-- Post-cursor state: payload length `P - Dst` and the header start. -/
def GS1 (DF : Nat) (Dst H0 : BitVec 64) (L G : GA) : Prop :=
  GBase Dst L ∧ HGe H0 G ∧ ∃ P : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧
    Dst.toNat ≤ P.toNat ∧ P.toNat ≤ DF + 8 ∧
    ∃ PL : BitVec 64, L.lookup (ofString "payload_len") = some (.val (.word PL))

def GS2 (DF : Nat) (Dst H0 : BitVec 64) (L G : GA) : Prop :=
  GS1 DF Dst H0 L G ∧ ∃ Hl : BitVec 64, L.lookup (ofString "hl") = some (.val (.word Hl)) ∧ Hl.toNat ≤ 9

def GS3 (K : Nat) (Lo : BitVec 64) (L G : GA) (H0 : BitVec 64) : Prop :=
  HGe H0 G ∧ (∃ PL : BitVec 64, L.lookup (ofString "payload_len") = some (.val (.word PL))) ∧
    ∃ St : BitVec 64, L.lookup (ofString "start") = some (.val (.word St)) ∧ Lo.toNat + K ≤ St.toNat ∧
      St.toNat ≤ 2 ^ 62 + 16

section gt
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {DF : Nat} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- The tail of the actual `tx_encode_generic` (mode-2 chain-id fields, list header placed backward below `Dst`,
the type byte): all stores land at or above `Lo` when `Lo + 10 ≤ Dst`. -/
theorem encTail_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64)
    (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (H0 : BitVec 64)
    (Dst : BitVec 64) (hLD : Lo.toNat + 10 ≤ Dst.toNat) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => CIG DF (GBase Dst) (HGe H0) Dst L G) (fun _ _ _ => False) (fun _ _ G => HGe H0 G) encTail := by
  unfold encTail
  have hbw := gbase_upd (Dst := Dst) (ofString "w") (by decide) (by decide)
  have hbp := gbase_upd (Dst := Dst) (ofString "p") (by decide) (by decide)
  -- mode 2: chain id, two empty strings
  refine aqgd_seq (aqgd_iteT _ ?_ aqgd_skip) ?_
  · refine aqgd_seq (csg_call (base := GBase Dst) Dst hbw _ _ _ _ _ originalRuntimeCode_rlpEncodeWord_lookup (by simp)
      (fun P L => L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "w") = some (.val (.word Y)))
      (fun P h1 h2 => cs_word hF hDF Lo hLo8 hw P (by omega) h2)
      (fun s values callee rs P b hp args lookup => hpe2 originalRuntimeCode_rlpEncodeWord_lookup (by decide)
        s _ P hp (fun v ev => by
          obtain ⟨_,c,hc⟩ := b
          simp [EV,evalHOLExact,hc] at ev; exact ⟨c,ev.symm⟩) args lookup))
      (aqgd_seq (csg_adv hDF Dst hbp) ?_)
    refine aqgd_seq (r_stbG (LP := fun L G => CIG DF (GBase Dst) (HGe H0) Dst L G)
      (LQ := fun L G => CIG DF (GBase Dst) (HGe H0) Dst L G) Lo hLo8 hw _ _ ?_) ?_
    · intro F s _ ⟨b,g,P,hp,h1,h2⟩
      exact ⟨P,by simp [EV,evalHOLExact,hp],by omega,fun _ => ⟨b,g,P,hp,h1,h2⟩⟩
    refine aqgd_seq (r_stbG (LP := fun L G => CIG DF (GBase Dst) (HGe H0) Dst L G)
      (LQ := fun L G => GBase Dst L ∧ HGe H0 G ∧ ∃ P : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧
        Dst.toNat ≤ P.toNat ∧ P.toNat + 2 ≤ DF + 8) Lo hLo8 hw _ _ ?_) ?_
    · intro F s _ ⟨b,g,P,hp,h1,h2⟩
      have e1 : (P + 1#64).toNat = P.toNat + 1 := by simp [BitVec.toNat_add]; omega
      refine ⟨P + 1#64,by simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord],
        by omega,fun hd => ?_⟩
      have := fence_byte hF hd
      exact ⟨b,g,P,hp,h1,by omega⟩
    · refine aqgd_assignLocal _ _ (fun s v _ _ ⟨b,g,P,hp,h1,h2⟩ _ ev => ?_)
      simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
      have e1 : (P + 2#64).toNat = P.toNat + 2 := by simp [BitVec.toNat_add]; omega
      exact ⟨hbp _ _ b,g,_,lookup_update_eq' _ _ _,by omega,by omega⟩
  -- payload_len = p - body
  refine aqgd_dec (Pb := fun L _ G => GS1 DF Dst H0 L G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s v _ _ hG ⟨b,g,P,hp,h1,h2⟩ _ ev _
    unfold GIs at hG; subst hG
    simp [EV,evalHOLExact,evalListHOLExact,hp,b.1,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    exact ⟨gbase_upd _ (by decide) (by decide) _ _ b,g,P,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,h1,h2,
      _,lookup_update_eq' _ _ _⟩
  -- hl = rlp_list_header_len(payload_len)
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (G0' : GA) (L : GA) (_ : Mem) (G : GA) =>
      L.lookup (ofString "payload_len") = some (.val (.word (wordOf L0 (ofString "payload_len")))) ∧ G = G0')
    (RRe := fun (_ : GA) (_ : Mem) (G0' : GA) (r : ValueHOL 64) (_ : Mem) (G' : GA) =>
      (∃ R : BitVec 64, r = .val (.word R) ∧ R.toNat ≤ 9) ∧ G' = G0')
    (Pc := fun L _ G => GS2 DF Dst H0 L G) (Qc := fun _ _ _ => False) _ _ _ _ _ _ _
    originalRuntimeCode_rlpListHeaderLen_lookup (by simp)
    (fun L0 _ G0' _ => aqgd_conseq (aqgd_ga (keepsGA_of_installed originalRuntimeCode_rlpListHeaderLen_lookup (by decide))
      (listHeaderLen_spec (wordOf L0 (ofString "payload_len"))) G0') (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim)
      (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ hG ⟨_,_,_,_,_,_,PL,hpl⟩ _ args lookup
    unfold GIs at hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hpl] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpListHeaderLen_lookup lookup
    rw [wordOf_eq hpl]
    exact ⟨by rw [e]; simp,rfl⟩
  · intro L M G v M' G' ⟨b,g,P,hp,h1,h2,PL,hpl⟩ ⟨⟨R,hr,hR⟩,hG⟩ _
    subst hr hG
    exact ⟨⟨gbase_upd _ (by decide) (by decide) _ _ b,g,P,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,h1,h2,
      PL,by rw [lookup_update_ne' _ _ (by decide)]; exact hpl⟩,R,lookup_update_eq' _ _ _,hR⟩
  -- start = body - hl
  refine aqgd_dec (Pb := fun L _ G => GS3 1 Lo L G H0) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s v _ _ hG ⟨⟨b,g,P,hp,h1,h2,PL,hpl⟩,Hl,hhl,hle⟩ _ ev _
    unfold GIs at hG; subst hG
    simp [EV,evalHOLExact,evalListHOLExact,hhl,b.1,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (Dst - Hl).toNat = Dst.toNat - Hl.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    exact ⟨g,⟨PL,by rw [lookup_update_ne' _ _ (by decide)]; exact hpl⟩,_,lookup_update_eq' _ _ _,by omega,by omega⟩
  -- rlp_encode_list_header(start, payload_len)
  refine aqgd_seq (Q := fun L _ G => GS3 1 Lo L G H0) (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (G0' : GA) (L : GA) (_ : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word (wordOf L0 (ofString "start")))) ∧
        L.lookup (ofString "payload_len") = some (.val (.word (wordOf L0 (ofString "payload_len"))))) ∧ G = G0')
    (RRe := fun (_ : GA) (_ : Mem) (G0' : GA) (_ : ValueHOL 64) (_ : Mem) (G' : GA) => G' = G0')
    _ _ _ _ _ originalRuntimeCode_rlpEncodeListHeader_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 _ G0' ⟨_,_,St,hst,h1,h2⟩
    rw [wordOf_eq hst]
    exact aqgd_conseq (aqgd_ga (keepsGA_of_installed originalRuntimeCode_rlpEncodeListHeader_lookup (by decide))
      (listHeader_win hF Lo hLo8 hw St (wordOf L0 (ofString "payload_len")) (by omega) (by omega)) G0')
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h.2)
  · intro F s values callee rs _ _ hG ⟨_,⟨PL,hpl⟩,St,hst,_⟩ _ args lookup
    unfold GIs at hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hpl,hst] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpEncodeListHeader_lookup lookup
    rw [wordOf_eq hpl,wordOf_eq hst]
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl⟩
  · intro L M G v M' G' pre hG
    subst hG; exact pre
  -- type byte, return
  refine aqgd_seq (Q := fun L _ G => GS3 0 Lo L G H0) (aqgd_iteT _ ?_
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ ⟨g,pl,St,hst,h1,h2⟩ => ⟨g,pl,St,hst,by omega,h2⟩)
      (fun _ _ _ h => h))) (aqgd_return _ ?_)
  · refine aqgd_seq (Q := fun L _ G => GS3 0 Lo L G H0) (aqgd_assignLocal _ _ ?_) (r_stbG (LP := fun L G => GS3 0 Lo L G H0)
      (LQ := fun L G => GS3 0 Lo L G H0) Lo hLo8 hw _ _ ?_)
    · intro F s v _ _ ⟨g,⟨PL,hpl⟩,St,hst,h1,h2⟩ _ ev
      simp [EV,evalHOLExact,evalListHOLExact,hst,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
      have e1 : (St - 1#64).toNat = St.toNat - 1 := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)
      exact ⟨g,⟨PL,by rw [lookup_update_ne' _ _ (by decide)]; exact hpl⟩,_,lookup_update_eq' _ _ _,by omega,by omega⟩
    · intro F s _ ⟨g,pl,St,hst,h1,h2⟩
      exact ⟨St,by simp [EV,evalHOLExact,hst],by omega,fun _ => ⟨g,pl,St,hst,h1,h2⟩⟩
  · intro F s v _ _ _ ⟨g,_⟩ _ _
    exact g

#print axioms encTail_win
end gt
section jn
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A journal-counter-keeping body moves from `JWS` with a pinned counter in the precondition to `JWSN`. -/
theorem aqgd_jwsn {P Q : GA → Mem → GA → Prop} {body : ProgHOL 64}
    (hk : keepsG (ofString "journal_n") goodJournalN body = true)
    (h : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w Vn
      (fun L M G => P L M G ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) Q RR body) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w Vn P Q RR body :=
  aqgd_preA (X := fun g => g.lookup (ofString "journal_n") = some (.val (.word Nj))) (fun _ h => h.2)
    (aqgd_strengthen (X := fun g => g.lookup (ofString "journal_n") = some (.val (.word Nj))) h
      (fun s code x => (evaluate_keeps_journal_n _ hk s code).trans x))

theorem fence_mono {D : BitVec 64 → Prop} {DF DF' : Nat} (h : Fence D DF) (le : DF ≤ DF') : Fence D DF' :=
  fun a ha => by have := h a ha; omega

#print axioms aqgd_jwsn
end jn

section gg
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {DF : Nat} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- The actual `tx_encode_generic(tx, mode, chain_id)` with the heap pointer at `H0`: every store lands at or above
`H0` (the fresh buffer, the field writers' cursor, the backward list header and type byte, and temporary heap
blocks), and the heap pointer stays at or above `H0`. -/
theorem encGeneric_win (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (H0 : BitVec 64)
    (hw : w.toNat < H0.toNat) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))) ∧ HeapIs G H0)
      (fun _ _ _ => False) (fun _ _ G => HGe H0 G) (sourceFunctionBody Guest.guestFn_tx_encode_generic) := by
  rw [geBody_eq]; unfold geBody
  refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H0.toNat ∧ H0.toNat ≤ 33806089496 ∧ H0.toNat % 8 = 0)
    (fun _ _ g aw ⟨_,hH⟩ => jws_heap_facts aw.1 hH) ?_
  intro ⟨hP0,hcapH,hal⟩
  have hF1 : Fence D (DF + 8) := fence_mono hF (by omega)
  let CH := fun (L : GA) => ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))
  have chu : ∀ (n : MlS), ofString "chain_id" ≠ n → ∀ L v, CH L → CH (L.update (n,v)) :=
    fun n hn L v ⟨c,h⟩ => ⟨c,by rw [lookup_update_ne' _ _ hn]; exact h⟩
  -- bound = tx_encode_bound(tx)
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => (CH L ∧ HeapIs G H0) ∧ ∃ Bd : BitVec 64, L.lookup (ofString "bound") = some (.val (.word Bd)))
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_txEncodeBound_lookup
    (fun _ M0' G0' _ => aqgd_of_mf (memoryFrame_of_good originalRuntimeCode_txEncodeBound_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_tx_encode_bound) (by body_check Guest.guestFn_tx_encode_bound) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro L M G v M' G' ⟨hc,hH⟩ ⟨_,e2⟩ ok
    subst e2
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    exact ⟨⟨chu _ (by decide) L _ hc,hH⟩,y,lookup_update_eq' _ _ _⟩
  -- buf = alloc(bound)
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (L0 : GA) (M0' : Mem) (_ : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "n") = some (.val (.word (wordOf L0 (ofString "bound")))) ∧ M = M0' ∧ HeapIs G H0)
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (v : ValueHOL 64) (_ : Mem) (G' : GA) => v = .val (.word H0) ∧ HGe H0 G')
    (Pc := fun L _ G => (CH L ∧ HGe H0 G) ∧ L.lookup (ofString "buf") = some (.val (.word H0)))
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h)
  · intro L0 M0' _ _
    refine aqgd_jwsn (keepsJournalN_of_installed originalRuntimeCode_allocation_lookup (by decide)) ?_
    refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) (wordOf L0 (ofString "bound")) H0 M0')))
      (keepsSkBuf_of_installed originalRuntimeCode_allocation_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨⟨hl,hM,hH⟩,hn⟩
      exact ⟨hn,H0,hH,hl,hM,rfl⟩
    · intro v M' G' ⟨_,H',hH',_,ev,_,_,c1,_⟩
      exact ⟨ev,H',hH',by omega⟩
  · intro F s values callee rs _ H' hG ⟨⟨_,hH⟩,Bd,hbd⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,hbd] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by rw [wordOf_eq hbd]; simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hH⟩
  · intro L M G v M' G' ⟨⟨hc,_⟩,_⟩ ⟨ev,hge⟩ _
    subst ev
    exact ⟨⟨chu _ (by decide) L _ hc,hge⟩,lookup_update_eq' _ _ _⟩
  -- body = buf + 10; p = body; t = tx[0]; w = 0
  have eB : (H0 + 10#64).toNat = H0.toNat + 10 := by simp [BitVec.toNat_add]; omega
  let BD := fun (L : GA) => L.lookup (ofString "body") = some (.val (.word (H0 + 10#64)))
  refine aqgd_dec (Pb := fun L _ G => (CH L ∧ HGe H0 G) ∧ BD L) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s v _ _ hG ⟨⟨hc,hge⟩,hb⟩ _ ev _
    unfold GIs at hG; subst hG
    simp [EV,evalHOLExact,evalListHOLExact,hb,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    exact ⟨⟨chu _ (by decide) _ _ hc,hge⟩,lookup_update_eq' _ _ _⟩
  refine aqgd_dec (Pb := fun L _ G => CIG (DF + 8) (GBase (H0 + 10#64)) (HGe H0) (H0 + 10#64) L G)
    (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s v _ _ hG ⟨⟨hc,hge⟩,hb⟩ _ ev _
    unfold GIs at hG; subst hG
    have hb' : s.locals.lookup (ofString "body") = some (.val (.word (H0 + 10#64))) := hb
    simp [EV,evalHOLExact] at ev; rw [hb'] at ev; simp only [Option.some.injEq] at ev; subst ev
    exact ⟨gbase_upd _ (by decide) (by decide) _ _ ⟨hb,hc⟩,hge,_,lookup_update_eq' _ _ _,le_refl _,by omega⟩
  have dec_keep : ∀ (n : MlS) (e : ExpHOL 64) {body : ProgHOL 64}, ofString "body" ≠ n → ofString "chain_id" ≠ n →
      ofString "p" ≠ n →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
        (fun L _ G => CIG (DF + 8) (GBase (H0 + 10#64)) (HGe H0) (H0 + 10#64) L G) (fun _ _ _ => False)
        (fun _ _ G => HGe H0 G) body →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
        (fun L _ G => CIG (DF + 8) (GBase (H0 + 10#64)) (HGe H0) (H0 + 10#64) L G) (fun _ _ _ => False)
        (fun _ _ G => HGe H0 G) (.dec n .one e body) :=
    fun n e body h1 h2 h3 hb => aqgd_dec (Pb := fun L _ G => CIG (DF + 8) (GBase (H0 + 10#64)) (HGe H0) (H0 + 10#64) L G)
      (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
      (fun s v _ _ hG ⟨b,g,P,hp,c1,c2⟩ _ _ _ => by
        unfold GIs at hG; subst hG
        exact ⟨gbase_upd _ h1 h2 _ _ b,g,P,by rw [lookup_update_ne' _ _ h3]; exact hp,c1,c2⟩) hb
      (fun _ _ _ _ _ _ _ h => h)
  refine dec_keep _ _ (by decide) (by decide) (by decide) (dec_keep _ _ (by decide) (by decide) (by decide) ?_)
  exact encMid_win hF1 hDF (by omega) H0 hal hw H0 (le_refl _) (H0 + 10#64) (by omega)
    (gbase_upd _ (by decide) (by decide)) (gbase_upd _ (by decide) (by decide))
    (encTail_win hF1 hDF H0 hal hw H0 (H0 + 10#64) (by omega))

#print axioms encGeneric_win
end gg
end InitECandidate.Runtime
