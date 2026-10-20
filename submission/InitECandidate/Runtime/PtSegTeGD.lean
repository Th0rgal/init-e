import InitECandidate.Runtime.PtNewBlkGD
import InitECandidate.Runtime.PtStoreGD
/-!
`process_transaction` spine drops 34-40: `te = te_new()` and the six stores into the fresh `te` block (`sender`, the
recipient word, the four-word value, `price`, `mgas`, `reservoir`), keeping the segment state `SI`. The block lies at
or above `Lo`; the stored values may have any shape (fenced any-shape store).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Local `name` is a word `X` at or above `Lo` with `X + N ≤ HEAP_END`. -/
def FB (name : MlS) (Lo : BitVec 64) (N : Nat) (L : GA) : Prop :=
  ∃ X : BitVec 64, L.lookup name = some (.val (.word X)) ∧ Lo.toNat ≤ X.toNat ∧ X.toNat + N ≤ 33806089496

theorem fb_upd {name : MlS} {Lo : BitVec 64} {N : Nat} {L : GA} (h : FB name Lo N L) (x : MlS) (v : ValueHOL 64)
    (hx : name ≠ x) : FB name Lo N (L.update (x,v)) :=
  let ⟨X,hX,a,b⟩ := h; ⟨X,by rw [lookup_update_ne' _ _ hx]; exact hX,a,b⟩

theorem fb_res {name : MlS} {Lo : BitVec 64} {N : Nat} {L : GA} (h : FB name Lo N L) (x : MlS)
    (o : Option (ValueHOL 64)) (hx : name ≠ x) : FB name Lo N (L.resVarEq (x,o)) :=
  let ⟨X,hX,a,b⟩ := h; ⟨X,by rw [resVarEq_lookup_ne' _ _ _ _ hx]; exact hX,a,b⟩

theorem fb_new {Lo Hb : BitVec 64} {N : Nat} (L : GA) (name : MlS) (h1 : Lo.toNat ≤ Hb.toNat)
    (h2 : Hb.toNat + N ≤ 33806089496) : FB name Lo N (L.update (name,.val (.word Hb))) :=
  ⟨Hb,lookup_update_eq' _ _ _,h1,h2⟩

theorem ev_addc {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (X k : BitVec 64)
    (h : s.locals.lookup name = some (.val (.word X))) :
    EV s (.op .add [.var .local name,.const k]) = some (.val (.word (X + k))) := by
  simp [EV,evalHOLExact,evalListHOLExact,h,wordOpHOL,wordOp,valueIsWord,valueWord]

section sf
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {Lo Nj : BitVec 64} {M0 : Mem}

/-- A store of any value at `name + k` into a fresh block `FB name Lo N` with `k < N` keeps `SI`. -/
theorem aqgd_stFB_si {LP : GA → Prop} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 64) (hw : w.toNat < Lo.toNat)
    (name : MlS) (N : Nat) (k : BitVec 64) (hk : k.toNat < N) (hfb : ∀ L, LP L → FB name Lo N L) (v : ExpHOL 64) :
    AQGD D B A w Vn (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
      (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) RR
      (.store (.op .add [.var .local name,.const k]) v) :=
  aqgd_storeAny_si hF hDF hw _ v (fun s _ lp => by
    obtain ⟨X,hX,lo,hi⟩ := hfb _ lp
    have e : (X + k).toNat = X.toNat + k.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨X + k,ev_addc s name X k hX,by omega,lp⟩)

#print axioms aqgd_stFB_si
end sf

section te
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Nj : BitVec 64} {M0 : Mem}

theorem teNew_inst : originalRuntimeCode.lookup (ofString "te_new") =
    some ([],newBlkBody (ofString "te") 200#64,.one) := by
  rw [← teNew_eq]; exact originalRuntimeCode_teNew_lookup

/-- Locals after `te = te_new()`: `index`, `sender`, and the fresh 200-byte `te` block. -/
def LTe (Ix S Lo : BitVec 64) (L : GA) : Prop :=
  LK [(ofString "index",Ix),(ofString "sender",S)] L ∧ FB (ofString "te") Lo 200 L

/-- Spine drops 34-40 of the actual `process_transaction`. -/
theorem ptSegTe {QM : Mem → GA → Prop} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hw : w.toNat < Lo.toNat)
    (Ix S : BitVec 64) {cont : ProgHOL 64}
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LK [(ofString "index",Ix),(ofString "sender",S)] L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
      (fun _ M G => QM M G) RR
      (.decCall (ofString "te") .one (ofString "te_new") []
        (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 0)]) (.var .local (ofString "sender")))
        (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 8)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 152)])))
        (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 16)]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "tx")),(.const 160)])))
        (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 48)]) (.var .local (ofString "price")))
        (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 80)]) (.var .local (ofString "mgas")))
        (.seq (.store (.op .add [(.var .local (ofString "te")),(.const 88)]) (.var .local (ofString "reservoir")))
          cont))))))) := by
  have hD : DF + 8 ≤ 2 ^ 64 := by omega
  have st := fun (k : BitVec 64) (hk : k.toNat < 200) (v : ExpHOL 64) =>
    aqgd_stFB_si (D := D) (B := B) (A := JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) (w := w) (Vn := fun _ => False)
      (RR := RR) (n := n) (c := c) (T := T) (Out := Out) (ko := ko) (Excl := Excl) (Nj := Nj) (M0 := M0)
      (LP := LTe Ix S Lo) hF hD hw (ofString "te") 200 k hk (fun _ h => h.2) v
  refine aqgd_decCall_newBlk_si (LP' := LTe Ix S Lo) _ _ _ 200#64 teNew_inst (by decide)
    (keepsBo_of_installed teNew_inst (by decide)) (keepsWs_of_installed teNew_inst (by decide))
    (keepsScr_of_installed teNew_inst (by decide)) hw
    (fun L Hb lp le hi _ => ⟨lk_update lp _ _ (by simp (config := {decide := true})),fb_new L _ le hi⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq (st 0#64 (by decide) _) ?_
  refine aqgd_seq (st 8#64 (by decide) _) ?_
  refine aqgd_seq (st 16#64 (by decide) _) ?_
  refine aqgd_seq (st 48#64 (by decide) _) ?_
  refine aqgd_seq (st 80#64 (by decide) _) ?_
  refine aqgd_seq (st 88#64 (by decide) _) hcont

#print axioms ptSegTe
end te
end InitECandidate.Runtime
