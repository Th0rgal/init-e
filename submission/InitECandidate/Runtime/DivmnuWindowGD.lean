import InitECandidate.Runtime.DivWinBase
import InitECandidate.Runtime.OriginalDivmodCode
import InitECandidate.Runtime.VmFn_nlz32
/-!
Window frame of the actual `divmnu` (Knuth long division on 32-bit digits): with the quotient and remainder buffers at
`U + 216`, `U + 352` and digit counts `1 ≤ n ≤ m ≤ 8`, every store lands in the 640-byte `u256_ws` workspace at `U`.
Locals-only step rules, the body split into loop chunks (`dmTop` … `dmW4`, tied to the source by `divmnu_body_eq`),
and `divmnu_window`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The 640-byte `u256_ws` workspace at `U`. -/
def WS (U x : BitVec 64) : Prop := U.toNat ≤ x.toNat ∧ x.toNat < U.toNat + 640

/-- The `u256_ws` global holds `U`. -/
def WsG (U : BitVec 64) (g : GA) : Prop := g.lookup (ofString "u256_ws") = some (.val (.word U))

theorem lookup_update_ne' (L : GA) {x name : MlS} (v : ValueHOL 64) (h : x ≠ name) :
    (L.update (name,v)).lookup x = L.lookup x := by
  simp [HolFiniteMapExact.lookup_update,FUPDATE]; intro e; exact absurd e.symm h

theorem lookup_update_eq' (L : GA) (name : MlS) (v : ValueHOL 64) : (L.update (name,v)).lookup name = some v := by
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

/-- Locals of `divmnu(q, r, u, m, v, n)` with the quotient and remainder digit buffers in the workspace, and bounds
on the loop counters `i`, `j`. -/
def DV (U Mm Nn : BitVec 64) (bi bj : Nat) (L : GA) : Prop :=
  L.lookup (ofString "q") = some (.val (.word (U + 216))) ∧ L.lookup (ofString "r") = some (.val (.word (U + 352))) ∧
    L.lookup (ofString "m") = some (.val (.word Mm)) ∧ L.lookup (ofString "n") = some (.val (.word Nn)) ∧
    (∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ bi) ∧
    (∃ J : BitVec 64, L.lookup (ofString "j") = some (.val (.word J)) ∧ J.toNat ≤ bj)

/-- `DV` with the normalised digit buffers `un = U`, `vn = U + 144`. -/
def DVU (U Mm Nn : BitVec 64) (bi bj : Nat) (L : GA) : Prop :=
  DV U Mm Nn bi bj L ∧ L.lookup (ofString "un") = some (.val (.word U)) ∧
    L.lookup (ofString "vn") = some (.val (.word (U + 144)))

/-- Names `DVU` reads. -/
def dvNames : List MlS :=
  [ofString "q",ofString "r",ofString "m",ofString "n",ofString "i",ofString "j",ofString "un",ofString "vn"]

/-- Names `DV` reads. -/
def dv0Names : List MlS :=
  [ofString "q",ofString "r",ofString "m",ofString "n",ofString "i",ofString "j"]

theorem notMem0 {name : MlS} (hn : name ∉ dvNames) : name ∉ dv0Names := by
  intro m; apply hn; simp only [dv0Names,dvNames,List.mem_cons,List.not_mem_nil,or_false] at m ⊢; tauto

theorem ne_of_notMem {x name : MlS} {l : List MlS} (hx : x ∈ l) (hn : name ∉ l) : x ≠ name :=
  fun e => hn (e ▸ hx)

theorem dv_upd {U Mm Nn : BitVec 64} {bi bj : Nat} {L : GA} (h : DV U Mm Nn bi bj L) (name : MlS) (v : ValueHOL 64)
    (hn : name ∉ dv0Names) : DV U Mm Nn bi bj (L.update (name,v)) := by
  obtain ⟨h1,h2,h3,h4,⟨I,hi,bI⟩,⟨J,hj,bJ⟩⟩ := h
  simp only [DV]
  rw [lookup_update_ne' _ _ (ne_of_notMem (by simp [dv0Names]) hn),lookup_update_ne' _ _ (ne_of_notMem (by simp [dv0Names]) hn),
    lookup_update_ne' _ _ (ne_of_notMem (by simp [dv0Names]) hn),lookup_update_ne' _ _ (ne_of_notMem (by simp [dv0Names]) hn),
    lookup_update_ne' _ _ (ne_of_notMem (by simp [dv0Names]) hn),lookup_update_ne' _ _ (ne_of_notMem (by simp [dv0Names]) hn)]
  exact ⟨h1,h2,h3,h4,⟨I,hi,bI⟩,⟨J,hj,bJ⟩⟩

theorem dvu_upd {U Mm Nn : BitVec 64} {bi bj : Nat} {L : GA} (h : DVU U Mm Nn bi bj L) (name : MlS) (v : ValueHOL 64)
    (hn : name ∉ dvNames) : DVU U Mm Nn bi bj (L.update (name,v)) := by
  obtain ⟨h0,h1,h2⟩ := h
  refine ⟨dv_upd h0 name v (notMem0 hn),?_,?_⟩
  · rw [lookup_update_ne' _ _ (ne_of_notMem (by simp [dvNames]) hn)]; exact h1
  · rw [lookup_update_ne' _ _ (ne_of_notMem (by simp [dvNames]) hn)]; exact h2

theorem dv_res {U Mm Nn : BitVec 64} {bi bj : Nat} {L : GA} (h : DV U Mm Nn bi bj L) (name : MlS)
    (o : Option (ValueHOL 64)) (hn : name ∉ dv0Names) : DV U Mm Nn bi bj (L.resVarEq (name,o)) := by
  obtain ⟨h1,h2,h3,h4,⟨I,hi,bI⟩,⟨J,hj,bJ⟩⟩ := h
  simp only [DV]
  rw [resVarEq_lookup_ne' _ _ _ _ (ne_of_notMem (by simp [dv0Names]) hn),
    resVarEq_lookup_ne' _ _ _ _ (ne_of_notMem (by simp [dv0Names]) hn),
    resVarEq_lookup_ne' _ _ _ _ (ne_of_notMem (by simp [dv0Names]) hn),
    resVarEq_lookup_ne' _ _ _ _ (ne_of_notMem (by simp [dv0Names]) hn),
    resVarEq_lookup_ne' _ _ _ _ (ne_of_notMem (by simp [dv0Names]) hn),
    resVarEq_lookup_ne' _ _ _ _ (ne_of_notMem (by simp [dv0Names]) hn)]
  exact ⟨h1,h2,h3,h4,⟨I,hi,bI⟩,⟨J,hj,bJ⟩⟩

theorem dvu_res {U Mm Nn : BitVec 64} {bi bj : Nat} {L : GA} (h : DVU U Mm Nn bi bj L) (name : MlS)
    (o : Option (ValueHOL 64)) (hn : name ∉ dvNames) : DVU U Mm Nn bi bj (L.resVarEq (name,o)) := by
  obtain ⟨h0,h1,h2⟩ := h
  refine ⟨dv_res h0 name o (notMem0 hn),?_,?_⟩
  · rw [resVarEq_lookup_ne' _ _ _ _ (ne_of_notMem (by simp [dvNames]) hn)]; exact h1
  · rw [resVarEq_lookup_ne' _ _ _ _ (ne_of_notMem (by simp [dvNames]) hn)]; exact h2

theorem dv_setI {U Mm Nn : BitVec 64} {bi bj : Nat} {L : GA} (h : DV U Mm Nn bi bj L) (bi' : Nat) (I : BitVec 64)
    (hI : I.toNat ≤ bi') : DV U Mm Nn bi' bj (L.update (ofString "i",.val (.word I))) := by
  obtain ⟨h1,h2,h3,h4,_,⟨J,hj,bJ⟩⟩ := h
  refine ⟨?_,?_,?_,?_,⟨I,lookup_update_eq' _ _ _,hI⟩,⟨J,?_,bJ⟩⟩ <;>
    (try rw [lookup_update_ne' _ _ (by decide)]) <;> assumption

theorem dv_setJ {U Mm Nn : BitVec 64} {bi bj : Nat} {L : GA} (h : DV U Mm Nn bi bj L) (bj' : Nat) (J : BitVec 64)
    (hJ : J.toNat ≤ bj') : DV U Mm Nn bi bj' (L.update (ofString "j",.val (.word J))) := by
  obtain ⟨h1,h2,h3,h4,⟨I,hi,bI⟩,_⟩ := h
  refine ⟨?_,?_,?_,?_,⟨I,?_,bI⟩,⟨J,lookup_update_eq' _ _ _,hJ⟩⟩ <;>
    (try rw [lookup_update_ne' _ _ (by decide)]) <;> assumption

theorem dvu_setI {U Mm Nn : BitVec 64} {bi bj : Nat} {L : GA} (h : DVU U Mm Nn bi bj L) (bi' : Nat) (I : BitVec 64)
    (hI : I.toNat ≤ bi') : DVU U Mm Nn bi' bj (L.update (ofString "i",.val (.word I))) :=
  ⟨dv_setI h.1 bi' I hI,by rw [lookup_update_ne' _ _ (by decide)]; exact h.2.1,
    by rw [lookup_update_ne' _ _ (by decide)]; exact h.2.2⟩

theorem dvu_setJ {U Mm Nn : BitVec 64} {bi bj : Nat} {L : GA} (h : DVU U Mm Nn bi bj L) (bj' : Nat) (J : BitVec 64)
    (hJ : J.toNat ≤ bj') : DVU U Mm Nn bi bj' (L.update (ofString "j",.val (.word J))) :=
  ⟨dv_setJ h.1 bj' J hJ,by rw [lookup_update_ne' _ _ (by decide)]; exact h.2.1,
    by rw [lookup_update_ne' _ _ (by decide)]; exact h.2.2⟩

theorem dv_mono {U Mm Nn : BitVec 64} {bi bj bi' bj' : Nat} {L : GA} (h : DV U Mm Nn bi bj L) (hi : bi ≤ bi')
    (hj : bj ≤ bj') : DV U Mm Nn bi' bj' L := by
  obtain ⟨h1,h2,h3,h4,⟨I,a,bI⟩,⟨J,b,bJ⟩⟩ := h
  exact ⟨h1,h2,h3,h4,⟨I,a,by omega⟩,⟨J,b,by omega⟩⟩

theorem dvu_mono {U Mm Nn : BitVec 64} {bi bj bi' bj' : Nat} {L : GA} (h : DVU U Mm Nn bi bj L) (hi : bi ≤ bi')
    (hj : bj ≤ bj') : DVU U Mm Nn bi' bj' L := ⟨dv_mono h.1 hi hj,h.2⟩

#print axioms dvu_upd
#print axioms dvu_res
section rules
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

theorem r_store (U : BitVec 64) {LP : GA → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → LP s.locals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ WS U a)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, A s.globals → LP s.locals → SL Vn s.locals →
      EV s v = some x → ∃ y : BitVec 64, x = .val (.word y))
    (hw : ¬ WS U w) : AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LP L) RR (.store d v) :=
  aqgd_storeD _ _ (fun s _ aw _ _ lp _ => let ⟨a,ha,hws⟩ := hd s aw lp; ⟨a,ha,fun e => hw (e ▸ hws),fun _ _ => lp⟩)
    (fun s x _ aw _ _ lp sl ev => hv s x aw lp sl ev)

theorem r_assign {LP LQ : GA → Prop} (x : MlS) (e : ExpHOL 64)
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, A s.globals → LP s.locals → EV s e = some v →
      LQ (s.locals.update (x,v))) :
    AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LQ L) RR (.assign .local x e) :=
  aqgd_assignLocal _ _ (fun s v aw _ pre _ ev => h s v aw pre ev)

theorem r_dec {LP LB LQ' LQ : GA → Prop} (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hshape : Vn name → shape = .one)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, A s.globals → LP s.locals → EV s init = some v →
      LB (s.locals.update (name,v)))
    (hb : AQGD D B A w Vn (fun L _ _ => LB L) (fun L _ _ => LQ' L) RR body)
    (hq : ∀ L L', LP L → LQ' L' → LQ (L'.resVarEq (name,L.lookup name))) :
    AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LQ L) RR (.dec name shape init body) :=
  aqgd_dec _ _ _ hshape (fun s v _ aw _ pre _ ev _ => hi s v aw pre ev) hb (fun L _ _ L' _ _ p q => hq L L' p q)

theorem r_decCall {LP LB LQ' LQ : GA → Prop} (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    {cont : ProgHOL 64} (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (hshape : Vn name → shape = .one)
    (hup : ∀ L v, LP L → shapeEqHOL (shapeOfHOLExact v) shape = true → LB (L.update (name,v)))
    (hb : AQGD D B A w Vn (fun L _ _ => LB L) (fun L _ _ => LQ' L) RR cont)
    (hq : ∀ L L', LP L → LQ' L' → LQ (L'.resVarEq (name,L.lookup name))) :
    AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LQ L) RR (.decCall name shape function arguments cont) :=
  aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    (Pc := fun L _ _ => LB L) (Qc := fun L _ _ => LQ' L) _ _ _ _ _ _ _ installed
    (fun _ M0' G0' _ => aqgd_of_mf mf nb nc M0' G0') (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) hshape
    (fun L _ _ v _ _ pre _ ok => hup L v pre ok) hb (fun L _ _ L' _ _ p q => hq L L' p q)

theorem r_while {LI LC : GA → Prop} (c : ExpHOL 64) {body : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → LI s.locals →
      EV s c = some (.val (.word x)) → x ≠ 0 → LC s.locals)
    (hb : AQGD D B A w Vn (fun L _ _ => LI L ∧ LC L) (fun L _ _ => LI L) RR body) :
    AQGD D B A w Vn (fun L _ _ => LI L) (fun L _ _ => LI L) RR (.while c body) :=
  aqgd_conseq (aqgd_whileBreak (I := fun L _ _ => LI L) (C := fun L _ _ => LC L) (Qb := fun _ _ _ => False) _
      (fun s x aw _ pre _ ev nz => hc s x aw pre ev nz) (aqgb_of_aqgd hb))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h)

theorem r_ite {LP LQ : GA → Prop} (c : ExpHOL 64) {y n : ProgHOL 64}
    (hy : AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LQ L) RR y)
    (hn : AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LQ L) RR n) :
    AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LQ L) RR (.ite c y n) :=
  aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aqgd_conseq hy (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    (aqgd_conseq hn (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))

#print axioms r_decCall
#print axioms r_while
end rules

theorem ev_shift_word {F : Type} (s : PanSemStateFiniteExact 64 F) (sh : Shift) (e n : ExpHOL 64) (x : ValueHOL 64)
    (h : EV s (.shift sh e n) = some x) : ∃ y : BitVec 64, x = .val (.word y) := by
  simp only [EV,evalHOLExact] at h
  split at h
  · obtain ⟨y,_,rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨y,rfl⟩
  · cases h

/-- `divmnu` chunk `dmW0`. -/
def dmW0 : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.const 0#64) (ExpHOL.var VarKind.local (ofString "j"))) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "j") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 1#64])) (ProgHOL.decCall (ofString "qr") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]) (ofString "div64by32") [ExpHOL.var VarKind.local (ofString "k"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "u"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 8#64]]), ExpHOL.var VarKind.local (ofString "d")] (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 8#64]]) (ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "qr")))) (ProgHOL.assign VarKind.local (ofString "k") (ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "qr")))))))

/-- `divmnu` chunk `dmW1`. -/
def dmW1 : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.const 0#64) (ExpHOL.var VarKind.local (ofString "i"))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "vn"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]]) (ExpHOL.op BinOp.and [ExpHOL.op BinOp.or [ExpHOL.shift Shift.lsl (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "v"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]])) (ExpHOL.var VarKind.local (ofString "s")), ExpHOL.shift Shift.lsr (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "v"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64], ExpHOL.const 8#64]])) (ExpHOL.op BinOp.sub [ExpHOL.const 32#64, ExpHOL.var VarKind.local (ofString "s")])], ExpHOL.const 4294967295#64])) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])))

/-- `divmnu` chunk `dmW2`. -/
def dmW2 : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.const 0#64) (ExpHOL.var VarKind.local (ofString "i"))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]]) (ExpHOL.op BinOp.and [ExpHOL.op BinOp.or [ExpHOL.shift Shift.lsl (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "u"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]])) (ExpHOL.var VarKind.local (ofString "s")), ExpHOL.shift Shift.lsr (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "u"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64], ExpHOL.const 8#64]])) (ExpHOL.op BinOp.sub [ExpHOL.const 32#64, ExpHOL.var VarKind.local (ofString "s")])], ExpHOL.const 4294967295#64])) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])))

/-- `divmnu` chunk `dmW3`. -/
def dmW3 : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "j")) (ExpHOL.var VarKind.local (ofString "m"))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 8#64]]) (ExpHOL.const 0#64)) (ProgHOL.assign VarKind.local (ofString "j") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 1#64])))

/-- `divmnu` chunk `dmW4`. -/
def dmW4 : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "r"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]]) (ExpHOL.op BinOp.or [ExpHOL.shift Shift.lsr (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]])) (ExpHOL.var VarKind.local (ofString "s")), ExpHOL.op BinOp.and [ExpHOL.shift Shift.lsl (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64], ExpHOL.const 8#64]])) (ExpHOL.op BinOp.sub [ExpHOL.const 32#64, ExpHOL.var VarKind.local (ofString "s")]), ExpHOL.const 4294967295#64]])) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])))

/-- `divmnu` chunk `dmLI2`. -/
def dmLI2 : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.dec (ofString "t2") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.var VarKind.local (ofString "j")], ExpHOL.const 8#64]]), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "vn"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]]), ExpHOL.var VarKind.local (ofString "k")]) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.var VarKind.local (ofString "j")], ExpHOL.const 8#64]]) (ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "t2"), ExpHOL.const 4294967295#64])) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "k") (ExpHOL.shift Shift.lsr (ExpHOL.var VarKind.local (ofString "t2")) (ExpHOL.const 32#64))) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])))))

/-- `divmnu` chunk `dmITT`. -/
def dmITT : ProgHOL 64 :=
  ProgHOL.ite (ExpHOL.cmp Cmp.less (ExpHOL.var VarKind.local (ofString "tt")) (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 8#64]]) (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "qhat"), ExpHOL.const 1#64])) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "k") (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.const 0#64)) (ProgHOL.seq dmLI2 (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.var VarKind.local (ofString "n")], ExpHOL.const 8#64]]) (ExpHOL.op BinOp.and [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tt"), ExpHOL.var VarKind.local (ofString "k")], ExpHOL.const 4294967295#64])))))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 8#64]]) (ExpHOL.var VarKind.local (ofString "qhat"))) (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.var VarKind.local (ofString "n")], ExpHOL.const 8#64]]) (ExpHOL.var VarKind.local (ofString "tt"))))

/-- `divmnu` chunk `dmLI`. -/
def dmLI : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.dec (ofString "p") ShapeHOL.one (ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "qhat"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "vn"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]])]) (ProgHOL.dec (ofString "t") ShapeHOL.one (ExpHOL.op BinOp.sub [ExpHOL.op BinOp.sub [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.var VarKind.local (ofString "j")], ExpHOL.const 8#64]]), ExpHOL.var VarKind.local (ofString "k")], ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 4294967295#64]]) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.var VarKind.local (ofString "j")], ExpHOL.const 8#64]]) (ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 4294967295#64])) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "k") (ExpHOL.op BinOp.sub [ExpHOL.shift Shift.lsr (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.const 32#64), ExpHOL.shift Shift.asr (ExpHOL.var VarKind.local (ofString "t")) (ExpHOL.const 32#64)])) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64]))))))

/-- `divmnu` chunk `dmAG`. -/
def dmAG : ProgHOL 64 :=
  ProgHOL.while (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "again")) (ExpHOL.const 1#64)) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "again") (ExpHOL.const 0#64)) (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "rhat")) (ExpHOL.const 4294967296#64)) (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.op BinOp.or [ExpHOL.shift Shift.lsl (ExpHOL.var VarKind.local (ofString "rhat")) (ExpHOL.const 32#64), ExpHOL.var VarKind.local (ofString "ujn2")]) (ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "qhat"), ExpHOL.var VarKind.local (ofString "vsec")])) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "qhat") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "qhat"), ExpHOL.const 1#64])) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "rhat") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "rhat"), ExpHOL.var VarKind.local (ofString "vtop")])) (ProgHOL.assign VarKind.local (ofString "again") (ExpHOL.const 1#64)))) ProgHOL.skip) ProgHOL.skip))

/-- `divmnu` chunk `dmQR`. -/
def dmQR : ProgHOL 64 :=
  ProgHOL.ite (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "ujn")) (ExpHOL.var VarKind.local (ofString "vtop"))) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "qhat") (ExpHOL.const 4294967295#64)) (ProgHOL.assign VarKind.local (ofString "rhat") (ExpHOL.op BinOp.sub [ExpHOL.op BinOp.or [ExpHOL.shift Shift.lsl (ExpHOL.var VarKind.local (ofString "ujn")) (ExpHOL.const 32#64), ExpHOL.var VarKind.local (ofString "ujn1")], ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "qhat"), ExpHOL.var VarKind.local (ofString "vtop")]]))) (ProgHOL.decCall (ofString "qr") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]) (ofString "div64by32") [ExpHOL.var VarKind.local (ofString "ujn"), ExpHOL.var VarKind.local (ofString "ujn1"), ExpHOL.var VarKind.local (ofString "vtop")] (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "qhat") (ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "qr")))) (ProgHOL.assign VarKind.local (ofString "rhat") (ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "qr"))))))

/-- `divmnu` chunk `dmMB`. -/
def dmMB : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "j") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 1#64])) (ProgHOL.dec (ofString "ujn") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.var VarKind.local (ofString "n")], ExpHOL.const 8#64]])) (ProgHOL.dec (ofString "ujn1") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.var VarKind.local (ofString "n")], ExpHOL.const 1#64], ExpHOL.const 8#64]])) (ProgHOL.dec (ofString "ujn2") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.var VarKind.local (ofString "n")], ExpHOL.const 2#64], ExpHOL.const 8#64]])) (ProgHOL.dec (ofString "qhat") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.dec (ofString "rhat") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq dmQR (ProgHOL.dec (ofString "again") ShapeHOL.one (ExpHOL.const 1#64) (ProgHOL.seq dmAG (ProgHOL.dec (ofString "k") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.const 0#64)) (ProgHOL.seq dmLI (ProgHOL.dec (ofString "tt") ShapeHOL.one (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "ujn"), ExpHOL.var VarKind.local (ofString "k")]) dmITT))))))))))))

/-- `divmnu` chunk `dmTAIL`. -/
def dmTAIL : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "j") (ExpHOL.op BinOp.add [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "m"), ExpHOL.var VarKind.local (ofString "n")], ExpHOL.const 1#64])) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.const 0#64) (ExpHOL.var VarKind.local (ofString "j"))) dmMB) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "j") (ExpHOL.op BinOp.add [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "m"), ExpHOL.var VarKind.local (ofString "n")], ExpHOL.const 1#64])) (ProgHOL.seq dmW3 (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.const 0#64)) (ProgHOL.seq dmW4 (ProgHOL.return (ExpHOL.const 0#64)))))))

/-- `divmnu` chunk `dmREST`. -/
def dmREST : ProgHOL 64 :=
  ProgHOL.dec (ofString "un") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "u256_ws"), ExpHOL.const 0#64]) (ProgHOL.dec (ofString "vn") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "u256_ws"), ExpHOL.const 144#64]) (ProgHOL.decCall (ofString "s") ShapeHOL.one (ofString "nlz32") [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "v"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "n"), ExpHOL.const 1#64], ExpHOL.const 8#64]])] (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "n"), ExpHOL.const 1#64])) (ProgHOL.seq dmW1 (ProgHOL.seq (ProgHOL.store (ExpHOL.var VarKind.local (ofString "vn")) (ExpHOL.op BinOp.and [ExpHOL.shift Shift.lsl (ExpHOL.load ShapeHOL.one (ExpHOL.var VarKind.local (ofString "v"))) (ExpHOL.var VarKind.local (ofString "s")), ExpHOL.const 4294967295#64])) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "m"), ExpHOL.const 8#64]]) (ExpHOL.shift Shift.lsr (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "u"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "m"), ExpHOL.const 1#64], ExpHOL.const 8#64]])) (ExpHOL.op BinOp.sub [ExpHOL.const 32#64, ExpHOL.var VarKind.local (ofString "s")]))) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "m"), ExpHOL.const 1#64])) (ProgHOL.seq dmW2 (ProgHOL.seq (ProgHOL.store (ExpHOL.var VarKind.local (ofString "un")) (ExpHOL.op BinOp.and [ExpHOL.shift Shift.lsl (ExpHOL.load ShapeHOL.one (ExpHOL.var VarKind.local (ofString "u"))) (ExpHOL.var VarKind.local (ofString "s")), ExpHOL.const 4294967295#64])) (ProgHOL.dec (ofString "vtop") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "vn"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "n"), ExpHOL.const 1#64], ExpHOL.const 8#64]])) (ProgHOL.dec (ofString "vsec") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "vn"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "n"), ExpHOL.const 2#64], ExpHOL.const 8#64]])) dmTAIL)))))))))))

/-- `divmnu` chunk `dmBR1`. -/
def dmBR1 : ProgHOL 64 :=
  ProgHOL.dec (ofString "d") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.var VarKind.local (ofString "v"))) (ProgHOL.dec (ofString "k") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "j") (ExpHOL.var VarKind.local (ofString "m"))) (ProgHOL.seq dmW0 (ProgHOL.seq (ProgHOL.store (ExpHOL.var VarKind.local (ofString "r")) (ExpHOL.var VarKind.local (ofString "k"))) (ProgHOL.return (ExpHOL.const 0#64))))))

/-- `divmnu` chunk `dmTop`. -/
def dmTop : ProgHOL 64 :=
  ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.dec (ofString "j") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "n")) (ExpHOL.const 1#64)) dmBR1 ProgHOL.skip) dmREST))

theorem divmnu_body_eq : sourceFunctionBody Guest.guestFn_divmnu = dmTop := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_divmnu,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

section dm
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {U Mm Nn : BitVec 64}

theorem dmW1_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hN8 : Nn.toNat ≤ 8) (hw : ¬ WS U w) (bj : Nat) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn (Nn.toNat - 1) bj L)
      (fun L _ _ => DVU U Mm Nn (Nn.toNat - 1) bj L) RR dmW1 := by
  unfold dmW1
  refine r_while (LC := fun L => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ 0 < I.toNat) _
    ?_ (aqgd_seq (r_store U (LP := fun L => DVU U Mm Nn (Nn.toNat - 1) bj L ∧
      ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ 0 < I.toNat) _ _ ?_ ?_ hw) (r_assign _ _ ?_))
  · intro F s x _ ⟨⟨_,_,_,_,⟨I,hi,_⟩,_⟩,_⟩ ev nz
    simp [EV,evalHOLExact,hi,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨I,hi,?_⟩
    by_cases h : (0#64 : BitVec 64) < I
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s _ ⟨⟨⟨_,_,_,_,⟨I,hi,bI⟩,_⟩,_,hvn⟩,_⟩
    refine ⟨U + 144#64 + I * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hi,hvn,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS
    simp [BitVec.toNat_add,BitVec.toNat_mul]
    omega
  · intro F s x _ _ _ ev; exact ev_op_word s _ _ x ev
  · intro F s v _ ⟨⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩,I',hi',pos⟩ ev
    rw [hi] at hi'; simp at hi'; subst hi'
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (I - 1).toNat = I.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
    exact dvu_setI ⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩ _ (I - 1) (by omega)

#print axioms dmW1_aqgd

theorem dmW2_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) (bj : Nat) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn (Mm.toNat - 1) bj L)
      (fun L _ _ => DVU U Mm Nn (Mm.toNat - 1) bj L) RR dmW2 := by
  unfold dmW2
  refine r_while (LC := fun L => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ 0 < I.toNat) _
    ?_ (aqgd_seq (r_store U (LP := fun L => DVU U Mm Nn (Mm.toNat - 1) bj L ∧
      ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ 0 < I.toNat) _ _ ?_ ?_ hw) (r_assign _ _ ?_))
  · intro F s x _ ⟨⟨_,_,_,_,⟨I,hi,_⟩,_⟩,_⟩ ev nz
    simp [EV,evalHOLExact,hi,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨I,hi,?_⟩
    by_cases h : (0#64 : BitVec 64) < I
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s _ ⟨⟨⟨_,_,_,_,⟨I,hi,bI⟩,_⟩,hun,_⟩,_⟩
    refine ⟨U + I * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hi,hun,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS
    simp [BitVec.toNat_add,BitVec.toNat_mul]
    omega
  · intro F s x _ _ _ ev; exact ev_op_word s _ _ x ev
  · intro F s v _ ⟨⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩,I',hi',pos⟩ ev
    rw [hi] at hi'; simp at hi'; subst hi'
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (I - 1).toNat = I.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
    exact dvu_setI ⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩ _ (I - 1) (by omega)

#print axioms dmW2_aqgd

theorem dmW3_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) (bi : Nat) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn bi Mm.toNat L)
      (fun L _ _ => DVU U Mm Nn bi Mm.toNat L) RR dmW3 := by
  unfold dmW3
  refine r_while (LC := fun L => ∃ J : BitVec 64, L.lookup (ofString "j") = some (.val (.word J)) ∧ J.toNat < Mm.toNat) _
    ?_ (aqgd_seq (r_store U (LP := fun L => DVU U Mm Nn bi Mm.toNat L ∧
      ∃ J : BitVec 64, L.lookup (ofString "j") = some (.val (.word J)) ∧ J.toNat < Mm.toNat) _ _ ?_ ?_ hw) (r_assign _ _ ?_))
  · intro F s x _ ⟨⟨_,_,hm,_,_,⟨J,hj,_⟩⟩,_⟩ ev nz
    simp [EV,evalHOLExact,hj,hm,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨J,hj,?_⟩
    by_cases h : J < Mm
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s _ ⟨⟨⟨hq,_,_,_,_,_⟩,_,_⟩,J,hj,lt⟩
    refine ⟨U + 216 + J * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hj,hq,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS
    simp [BitVec.toNat_add,BitVec.toNat_mul]
    omega
  · intro F s x _ _ _ ev; simp [EV,evalHOLExact] at ev; exact ⟨_,ev.symm⟩
  · intro F s v _ ⟨⟨⟨h1,h2,h3,h4,hi,⟨J,hj,bJ⟩⟩,hun,hvn⟩,J',hj',lt⟩ ev
    rw [hj] at hj'; simp at hj'; subst hj'
    simp [EV,evalHOLExact,evalListHOLExact,hj,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (J + 1).toNat = J.toNat + 1 := by simp [BitVec.toNat_add]; omega
    exact dvu_setJ ⟨⟨h1,h2,h3,h4,hi,⟨J,hj,bJ⟩⟩,hun,hvn⟩ _ (J + 1) (by omega)

theorem dmW4_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hN8 : Nn.toNat ≤ 8) (hw : ¬ WS U w) (bj : Nat) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn Nn.toNat bj L)
      (fun L _ _ => DVU U Mm Nn Nn.toNat bj L) RR dmW4 := by
  unfold dmW4
  refine r_while (LC := fun L => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < Nn.toNat) _
    ?_ (aqgd_seq (r_store U (LP := fun L => DVU U Mm Nn Nn.toNat bj L ∧
      ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < Nn.toNat) _ _ ?_ ?_ hw) (r_assign _ _ ?_))
  · intro F s x _ ⟨⟨_,_,_,hn,⟨I,hi,_⟩,_⟩,_⟩ ev nz
    simp [EV,evalHOLExact,hi,hn,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨I,hi,?_⟩
    by_cases h : I < Nn
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s _ ⟨⟨⟨_,hr,_,_,_,_⟩,_,_⟩,I,hi,lt⟩
    refine ⟨U + 352 + I * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hi,hr,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS
    simp [BitVec.toNat_add,BitVec.toNat_mul]
    omega
  · intro F s x _ _ _ ev; exact ev_op_word s _ _ x ev
  · intro F s v _ ⟨⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩,I',hi',lt⟩ ev
    rw [hi] at hi'; simp at hi'; subst hi'
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (I + 1).toNat = I.toNat + 1 := by simp [BitVec.toNat_add]; omega
    exact dvu_setI ⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩ _ (I + 1) (by omega)


/-- `qr` holds a pair of words. -/
def QRP (L : GA) : Prop :=
  ∃ a b : BitVec 64, L.lookup (ofString "qr") = some (.rStruct [.val (.word a),.val (.word b)])

theorem dmW0_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) (bi : Nat) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DV U Mm Nn bi Mm.toNat L)
      (fun L _ _ => DV U Mm Nn bi Mm.toNat L) RR dmW0 := by
  unfold dmW0
  refine r_while (LC := fun L => ∃ J : BitVec 64, L.lookup (ofString "j") = some (.val (.word J)) ∧ 0 < J.toNat) _
    ?_ (aqgd_seq (r_assign (LQ := fun L => DV U Mm Nn bi (Mm.toNat - 1) L) _ _ ?_)
      (r_decCall (LB := fun L => DV U Mm Nn bi (Mm.toNat - 1) L ∧ QRP L) (LQ' := fun L => DV U Mm Nn bi Mm.toNat L)
        _ _ _ _ _ _ _ originalRuntimeCode_div64by32_lookup
        (memoryFrame_of_good originalRuntimeCode_div64by32_lookup (by decide) (by decide))
        (by body_check Guest.guestFn_div64by32) (by body_check Guest.guestFn_div64by32) (fun h => absurd rfl h)
        (fun L v lp ok => ⟨dv_upd lp _ v (by decide),by
          obtain ⟨a,b,rfl⟩ := pair_of_shape ok
          exact ⟨a,b,lookup_update_eq' _ _ _⟩⟩)
        (aqgd_seq (r_store U _ _ ?_ ?_ hw) (r_assign _ _ ?_)) (fun L L' _ h => dv_res h _ _ (by decide))))
  · intro F s x _ ⟨_,_,_,_,_,⟨J,hj,_⟩⟩ ev nz
    simp [EV,evalHOLExact,hj,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨J,hj,?_⟩
    by_cases h : (0#64 : BitVec 64) < J
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s v _ ⟨⟨h1,h2,h3,h4,hi,⟨J,hj,bJ⟩⟩,J',hj',pos⟩ ev
    rw [hj] at hj'; simp at hj'; subst hj'
    simp [EV,evalHOLExact,evalListHOLExact,hj,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (J - 1).toNat = J.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
    exact dv_setJ ⟨h1,h2,h3,h4,hi,⟨J,hj,bJ⟩⟩ _ (J - 1) (by omega)
  · intro F s _ ⟨⟨hq,_,_,_,_,⟨J,hj,bJ⟩⟩,_⟩
    refine ⟨U + 216 + J * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hj,hq,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS
    simp [BitVec.toNat_add,BitVec.toNat_mul]
    omega
  · intro F s x _ ⟨_,a,b,hqr⟩ _ ev
    simp [EV,evalHOLExact,hqr] at ev; exact ⟨a,ev.symm⟩
  · intro F s v _ ⟨lp,_⟩ _
    exact dv_mono (dv_upd lp _ v (by decide)) (le_refl _) (by omega)

#print axioms dmW0_aqgd

theorem dmBR1_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) (bi bj : Nat) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DV U Mm Nn bi bj L) (fun _ _ _ => False)
      (fun _ _ _ => True) dmBR1 := by
  unfold dmBR1
  refine r_dec (LB := fun L => DV U Mm Nn bi bj L) (LQ' := fun _ => False) _ _ _ (fun _ => rfl)
    (fun s v _ lp _ => dv_upd lp _ v (by decide)) ?_ (fun _ _ _ h => h)
  refine r_dec (LB := fun L => DV U Mm Nn bi bj L) (LQ' := fun _ => False) _ _ _ (fun _ => rfl)
    (fun s v _ lp _ => dv_upd lp _ v (by decide)) ?_ (fun _ _ _ h => h)
  refine aqgd_seq (r_assign (LQ := fun L => DV U Mm Nn bi Mm.toNat L) _ _ ?_)
    (aqgd_seq (dmW0_aqgd hU hM8 hw bi) (aqgd_seq (r_store U _ _ ?_ ?_ hw) (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial))))
  · intro F s v _ ⟨h1,h2,h3,h4,hi,hj⟩ ev
    simp [EV,evalHOLExact,h3] at ev; subst ev
    exact dv_setJ ⟨h1,h2,h3,h4,hi,hj⟩ _ Mm (le_refl _)
  · intro F s _ ⟨_,hr,_,_,_,_⟩
    refine ⟨U + 352,by simp [EV,evalHOLExact,hr],?_⟩
    unfold WS
    simp [BitVec.toNat_add]
    omega
  · intro F s x _ _ sl ev
    simp [EV,evalHOLExact] at ev
    exact sl _ (by decide) x ev

#print axioms dmBR1_aqgd
theorem r_assign_dvu {bi bj : Nat} (x : MlS) (e : ExpHOL 64) (hx : x ∉ dvNames) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn bi bj L) (fun L _ _ => DVU U Mm Nn bi bj L) RR
      (.assign .local x e) :=
  r_assign _ _ (fun _ v _ lp _ => dvu_upd lp _ v hx)

/-- The two inner digit loops of the main `divmnu` step: `un[i+j]` for `i < n`. -/
theorem dmLI_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hNM : Nn.toNat ≤ Mm.toNat) (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L)
      (fun L _ _ => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L) RR dmLI := by
  unfold dmLI
  refine r_while (LC := fun L => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < Nn.toNat) _
    ?_ ?_
  · intro F s x _ ⟨⟨_,_,_,hn,⟨I,hi,_⟩,_⟩,_⟩ ev nz
    simp [EV,evalHOLExact,hi,hn,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨I,hi,?_⟩
    by_cases h : I < Nn
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  let LIP := fun L => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L ∧
    ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < Nn.toNat
  refine r_dec (LB := LIP) (LQ' := fun L => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L) _ _ _ (fun _ => rfl)
    (fun s v _ ⟨lp,I,hi,lt⟩ _ => ⟨dvu_upd lp _ v (by decide),I,by rw [lookup_update_ne' _ _ (by decide)]; exact hi,lt⟩)
    ?_ (fun _ _ _ h => dvu_res h _ _ (by decide))
  refine r_dec (LB := LIP) (LQ' := fun L => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L) _ _ _ (fun _ => rfl)
    (fun s v _ ⟨lp,I,hi,lt⟩ _ => ⟨dvu_upd lp _ v (by decide),I,by rw [lookup_update_ne' _ _ (by decide)]; exact hi,lt⟩)
    ?_ (fun _ _ _ h => dvu_res h _ _ (by decide))
  refine aqgd_seq (r_store U (LP := LIP) _ _ ?_ ?_ hw) (aqgd_seq (r_assign (LQ := LIP) _ _ ?_) (r_assign _ _ ?_))
  · intro F s _ ⟨⟨⟨_,_,_,_,_,⟨J,hj,bJ⟩⟩,hun,_⟩,I,hi,lt⟩
    refine ⟨U + (I + J) * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hi,hj,hun,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS
    simp [BitVec.toNat_add,BitVec.toNat_mul]
    omega
  · intro F s x _ _ _ ev; exact ev_op_word s _ _ x ev
  · intro F s v _ ⟨lp,I,hi,lt⟩ _
    exact ⟨dvu_upd lp _ v (by decide),I,by rw [lookup_update_ne' _ _ (by decide)]; exact hi,lt⟩
  · intro F s v _ ⟨⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩,I',hi',lt⟩ ev
    rw [hi] at hi'; simp at hi'; subst hi'
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (I + 1).toNat = I.toNat + 1 := by simp [BitVec.toNat_add]; omega
    exact dvu_setI ⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩ _ (I + 1) (by omega)

#print axioms dmLI_aqgd
theorem r_dec_dvu {bi bj bi' bj' : Nat} (name : MlS) (init : ExpHOL 64) {body : ProgHOL 64} (hx : name ∉ dvNames)
    (hb : AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn bi bj L)
      (fun L _ _ => DVU U Mm Nn bi' bj' L) RR body) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn bi bj L)
      (fun L _ _ => DVU U Mm Nn bi' bj' L) RR (.dec name .one init body) :=
  r_dec _ _ _ (fun _ => rfl) (fun _ v _ lp _ => dvu_upd lp _ v hx) hb (fun _ _ _ h => dvu_res h _ _ hx)

theorem dmLI2_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hNM : Nn.toNat ≤ Mm.toNat) (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L)
      (fun L _ _ => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L) RR dmLI2 := by
  unfold dmLI2
  refine r_while (LC := fun L => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < Nn.toNat) _
    ?_ ?_
  · intro F s x _ ⟨⟨_,_,_,hn,⟨I,hi,_⟩,_⟩,_⟩ ev nz
    simp [EV,evalHOLExact,hi,hn,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨I,hi,?_⟩
    by_cases h : I < Nn
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  let LIP := fun L => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L ∧
    ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < Nn.toNat
  refine r_dec (LB := LIP) (LQ' := fun L => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L) _ _ _ (fun _ => rfl)
    (fun s v _ ⟨lp,I,hi,lt⟩ _ => ⟨dvu_upd lp _ v (by decide),I,by rw [lookup_update_ne' _ _ (by decide)]; exact hi,lt⟩)
    ?_ (fun _ _ _ h => dvu_res h _ _ (by decide))
  refine aqgd_seq (r_store U (LP := LIP) _ _ ?_ ?_ hw) (aqgd_seq (r_assign (LQ := LIP) _ _ ?_) (r_assign _ _ ?_))
  · intro F s _ ⟨⟨⟨_,_,_,_,_,⟨J,hj,bJ⟩⟩,hun,_⟩,I,hi,lt⟩
    refine ⟨U + (I + J) * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hi,hj,hun,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS
    simp [BitVec.toNat_add,BitVec.toNat_mul]
    omega
  · intro F s x _ _ _ ev; exact ev_op_word s _ _ x ev
  · intro F s v _ ⟨lp,I,hi,lt⟩ _
    exact ⟨dvu_upd lp _ v (by decide),I,by rw [lookup_update_ne' _ _ (by decide)]; exact hi,lt⟩
  · intro F s v _ ⟨⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩,I',hi',lt⟩ ev
    rw [hi] at hi'; simp at hi'; subst hi'
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (I + 1).toNat = I.toNat + 1 := by simp [BitVec.toNat_add]; omega
    exact dvu_setI ⟨⟨h1,h2,h3,h4,⟨I,hi,bI⟩,hj⟩,hun,hvn⟩ _ (I + 1) (by omega)

#print axioms dmLI2_aqgd

theorem dmITT_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hNM : Nn.toNat ≤ Mm.toNat) (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L)
      (fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L) RR dmITT := by
  unfold dmITT
  have qst : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals →
      DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) s.locals →
      ∃ a : BitVec 64, EV s (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "q"),
        ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 8#64]]) = some (.val (.word a)) ∧
        WS U a := by
    intro F s _ ⟨⟨hq,_,_,_,_,⟨J,hj,bJ⟩⟩,_,_⟩
    refine ⟨U + 216 + J * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hj,hq,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS; simp [BitVec.toNat_add,BitVec.toNat_mul]; omega
  have ust : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals →
      DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) s.locals →
      ∃ a : BitVec 64, EV s (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "un"),
        ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "j"),
          ExpHOL.var VarKind.local (ofString "n")], ExpHOL.const 8#64]]) = some (.val (.word a)) ∧ WS U a := by
    intro F s _ ⟨⟨_,_,_,hn,_,⟨J,hj,bJ⟩⟩,hun,_⟩
    refine ⟨U + (J + Nn) * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hj,hn,hun,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS; simp [BitVec.toNat_add,BitVec.toNat_mul]; omega
  refine r_ite _ ?_ ?_
  · refine aqgd_seq (r_store U _ _ qst (fun s x _ _ _ ev => ev_op_word s _ _ x ev) hw)
      (aqgd_seq (r_assign_dvu _ _ (by decide))
        (aqgd_seq (r_assign (LQ := fun L => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L) _ _ ?_)
          (aqgd_seq (aqgd_conseq (dmLI2_aqgd hU hNM hM8 hw) (fun _ _ _ h => h)
            (fun _ _ _ h => dvu_mono h hNM (le_refl _)) (fun _ _ _ h => h))
            (r_store U _ _ ust (fun s x _ _ _ ev => ev_op_word s _ _ x ev) hw))))
    intro F s v _ lp ev
    simp [EV,evalHOLExact] at ev; subst ev
    exact dvu_setI lp _ 0 (by simp)
  · exact aqgd_seq (r_store U _ _ qst (fun s x _ _ sl ev => by simp [EV,evalHOLExact] at ev; exact sl _ (by decide) x ev) hw)
      (r_store U _ _ ust (fun s x _ _ sl ev => by simp [EV,evalHOLExact] at ev; exact sl _ (by decide) x ev) hw)

#print axioms dmITT_aqgd

theorem dmAG_aqgd :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L)
      (fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L) RR dmAG := by
  unfold dmAG
  refine r_while (LC := fun _ => True) _ (fun _ _ _ _ _ _ => trivial) ?_
  refine aqgd_conseq (P := (fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L)) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
  exact aqgd_seq (r_assign_dvu _ _ (by decide)) (r_ite _ (r_ite _ (aqgd_seq (r_assign_dvu _ _ (by decide))
    (aqgd_seq (r_assign_dvu _ _ (by decide)) (r_assign_dvu _ _ (by decide)))) aqgd_skip) aqgd_skip)

#print axioms dmAG_aqgd

theorem dmQR_aqgd :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L)
      (fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L) RR dmQR := by
  unfold dmQR
  exact r_ite _ (aqgd_seq (r_assign_dvu _ _ (by decide)) (r_assign_dvu _ _ (by decide)))
    (r_decCall _ _ _ _ _ _ _ originalRuntimeCode_div64by32_lookup
      (memoryFrame_of_good originalRuntimeCode_div64by32_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_div64by32) (by body_check Guest.guestFn_div64by32) (fun h => absurd rfl h)
      (fun L v lp _ => dvu_upd lp _ v (by decide))
      (aqgd_seq (r_assign_dvu _ _ (by decide)) (r_assign_dvu _ _ (by decide))) (fun _ _ _ h => dvu_res h _ _ (by decide)))

#print axioms dmQR_aqgd
theorem dmMB_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hN1 : 1 ≤ Nn.toNat) (hNM : Nn.toNat ≤ Mm.toNat)
    (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) :
    AQGD D B A w (fun x => x ≠ ofString "qr")
      (fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat + 1) L ∧
        ∃ J : BitVec 64, L.lookup (ofString "j") = some (.val (.word J)) ∧ 0 < J.toNat)
      (fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat + 1) L) RR dmMB := by
  unfold dmMB
  refine aqgd_seq (r_assign (LQ := fun L => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L) _ _ ?_)
    (aqgd_conseq (P := fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L)
      (Q := fun L _ _ => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L) ?_ (fun _ _ _ h => h)
      (fun _ _ _ h => dvu_mono h (le_refl _) (by omega)) (fun _ _ _ h => h))
  · intro F s v _ ⟨⟨⟨h1,h2,h3,h4,hi,⟨J,hj,bJ⟩⟩,hun,hvn⟩,J',hj',pos⟩ ev
    rw [hj] at hj'; simp at hj'; subst hj'
    simp [EV,evalHOLExact,evalListHOLExact,hj,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (J - 1).toNat = J.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
    exact dvu_setJ ⟨⟨h1,h2,h3,h4,hi,⟨J,hj,bJ⟩⟩,hun,hvn⟩ (Mm.toNat - Nn.toNat) (J - 1) (by omega)
  refine r_dec_dvu _ _ ?_ ?_
  · decide
  refine r_dec_dvu _ _ ?_ ?_
  · decide
  refine r_dec_dvu _ _ ?_ ?_
  · decide
  refine r_dec_dvu _ _ ?_ ?_
  · decide
  refine r_dec_dvu _ _ ?_ ?_
  · decide
  refine aqgd_seq dmQR_aqgd ?_
  refine r_dec_dvu _ _ ?_ ?_
  · decide
  refine aqgd_seq dmAG_aqgd ?_
  refine r_dec_dvu _ _ ?_ ?_
  · decide
  refine aqgd_seq (r_assign (LQ := fun L => DVU U Mm Nn Nn.toNat (Mm.toNat - Nn.toNat) L) _ _ ?_)
    (aqgd_seq (dmLI_aqgd hU hNM hM8 hw)
      (r_dec (LB := fun L => DVU U Mm Nn Mm.toNat (Mm.toNat - Nn.toNat) L) _ _ _ (fun _ => rfl)
        (fun _ v _ lp _ => dvu_mono (dvu_upd lp _ v (by decide)) hNM (le_refl _)) (dmITT_aqgd hU hNM hM8 hw)
        (fun _ _ _ h => dvu_res h _ _ (by decide))))
  intro F s v _ lp ev
  simp [EV,evalHOLExact] at ev; subst ev
  exact dvu_setI lp _ 0 (by simp)

#print axioms dmMB_aqgd

theorem dmTAIL_aqgd (hU : U.toNat + 640 ≤ 2 ^ 64) (hN1 : 1 ≤ Nn.toNat) (hNM : Nn.toNat ≤ Mm.toNat)
    (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) (bj : Nat) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVU U Mm Nn Mm.toNat bj L) (fun _ _ _ => False)
      (fun _ _ _ => True) dmTAIL := by
  unfold dmTAIL
  have jset : ∀ {bi bj' : Nat} {F : Type} (s : PanSemStateFiniteExact 64 F) v, DVU U Mm Nn bi bj' s.locals →
      EV s (ExpHOL.op BinOp.add [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "m"),
        ExpHOL.var VarKind.local (ofString "n")], ExpHOL.const 1#64]) = some v →
      DVU U Mm Nn bi (Mm.toNat - Nn.toNat + 1) (s.locals.update (ofString "j",v)) := by
    intro bi bj' F s v ⟨⟨h1,h2,h3,h4,hi,hj⟩,hun,hvn⟩ ev
    simp [EV,evalHOLExact,evalListHOLExact,h3,h4,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    refine dvu_setJ ⟨⟨h1,h2,h3,h4,hi,hj⟩,hun,hvn⟩ _ _ ?_
    have : (Mm - Nn).toNat = Mm.toNat - Nn.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    simp [BitVec.toNat_add,this]; omega
  refine aqgd_seq (r_assign _ _ (fun s v _ lp ev => jset s v lp ev))
    (aqgd_seq (r_while (LC := fun L => ∃ J : BitVec 64, L.lookup (ofString "j") = some (.val (.word J)) ∧ 0 < J.toNat) _
      ?_ (dmMB_aqgd hU hN1 hNM hM8 hw))
      (aqgd_seq (r_assign (LQ := fun L => DVU U Mm Nn Mm.toNat Mm.toNat L) _ _
          (fun s v _ lp ev => dvu_mono (jset s v lp ev) (le_refl _) (by omega)))
        (aqgd_seq (dmW3_aqgd hU hM8 hw _)
          (aqgd_seq (r_assign (LQ := fun L => DVU U Mm Nn Nn.toNat Mm.toNat L) _ _ ?_)
            (aqgd_seq (dmW4_aqgd hU (by omega) hw _) (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)))))))
  · intro F s x _ ⟨⟨_,_,_,_,_,⟨J,hj,_⟩⟩,_⟩ ev nz
    simp [EV,evalHOLExact,hj,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨J,hj,?_⟩
    by_cases h : (0#64 : BitVec 64) < J
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s v _ lp ev
    simp [EV,evalHOLExact] at ev; subst ev
    exact dvu_setI lp _ 0 (by simp)

#print axioms dmTAIL_aqgd
theorem dmREST_aqgd (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hN1 : 1 ≤ Nn.toNat)
    (hNM : Nn.toNat ≤ Mm.toNat) (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) (bi bj : Nat) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DV U Mm Nn bi bj L) (fun _ _ _ => False)
      (fun _ _ _ => True) dmREST := by
  unfold dmREST
  refine r_dec (LB := fun L => DV U Mm Nn bi bj L ∧ L.lookup (ofString "un") = some (.val (.word U)))
    (LQ' := fun _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v aw lp ev
    have hg := hA _ aw
    unfold WsG at hg
    simp [EV,evalHOLExact,evalListHOLExact,hg,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    exact ⟨dv_upd lp _ _ (by decide),lookup_update_eq' _ _ _⟩
  refine r_dec (LB := fun L => DVU U Mm Nn bi bj L) (LQ' := fun _ => False) _ _ _ (fun _ => rfl) ?_ ?_
    (fun _ _ _ h => h)
  · intro F s v aw ⟨lp,hun⟩ ev
    have hg := hA _ aw
    unfold WsG at hg
    simp [EV,evalHOLExact,evalListHOLExact,hg,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    exact ⟨dv_upd lp _ _ (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact hun,lookup_update_eq' _ _ _⟩
  refine r_decCall (LB := fun L => DVU U Mm Nn bi bj L) (LQ' := fun _ => False) _ _ _ _ _ _ _ vmLookup_nlz32
    (memoryFrame_of_good vmLookup_nlz32 (by decide) (by decide)) (by body_check Guest.guestFn_nlz32)
    (by body_check Guest.guestFn_nlz32) (fun _ => rfl) (fun L v lp _ => dvu_upd lp _ v (by decide)) ?_
    (fun _ _ _ h => h)
  refine aqgd_seq (r_assign (LQ := fun L => DVU U Mm Nn (Nn.toNat - 1) bj L) _ _ ?_) ?_
  · intro F s v _ lp ev
    have h4 := lp.1.2.2.2.1
    simp [EV,evalHOLExact,evalListHOLExact,h4,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    refine dvu_setI lp _ _ ?_
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  refine aqgd_seq (dmW1_aqgd hU (by omega) hw bj) ?_
  refine aqgd_seq (r_store U _ _ ?_ (fun s x _ _ _ ev => ev_op_word s _ _ x ev) hw) ?_
  · intro F s _ ⟨_,_,hvn⟩
    refine ⟨U + 144,by simp [EV,evalHOLExact,hvn],?_⟩
    unfold WS; simp [BitVec.toNat_add]; omega
  refine aqgd_seq (r_store U _ _ ?_ (fun s x _ _ _ ev => ev_shift_word s _ _ _ x ev) hw) ?_
  · intro F s _ ⟨⟨_,_,hm,_,_,_⟩,hun,_⟩
    refine ⟨U + Mm * 8#64,by simp [EV,evalHOLExact,evalListHOLExact,hm,hun,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],?_⟩
    unfold WS; simp [BitVec.toNat_add,BitVec.toNat_mul]; omega
  refine aqgd_seq (r_assign (LQ := fun L => DVU U Mm Nn (Mm.toNat - 1) bj L) _ _ ?_) ?_
  · intro F s v _ lp ev
    have h3 := lp.1.2.2.1
    simp [EV,evalHOLExact,evalListHOLExact,h3,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    refine dvu_setI lp _ _ ?_
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  refine aqgd_seq (dmW2_aqgd hU hM8 hw bj) ?_
  refine aqgd_seq (r_store U _ _ ?_ (fun s x _ _ _ ev => ev_op_word s _ _ x ev) hw) ?_
  · intro F s _ ⟨_,hun,_⟩
    refine ⟨U,by simp [EV,evalHOLExact,hun],?_⟩
    unfold WS; omega
  refine r_dec (LB := fun L => DVU U Mm Nn (Mm.toNat - 1) bj L) (LQ' := fun _ => False) _ _ _ (fun _ => rfl)
    (fun _ v _ lp _ => dvu_upd lp _ v (by decide)) ?_ (fun _ _ _ h => h)
  refine r_dec (LB := fun L => DVU U Mm Nn Mm.toNat bj L) (LQ' := fun _ => False) _ _ _ (fun _ => rfl)
    (fun _ v _ lp _ => dvu_mono (dvu_upd lp _ v (by decide)) (by omega) (le_refl _)) ?_ (fun _ _ _ h => h)
  exact dmTAIL_aqgd hU hN1 hNM hM8 hw bj

#print axioms dmREST_aqgd

/-- Entry locals of `divmnu(q, r, u, m, v, n)` as called from `digits_divmod`. -/
def DVP (U Mm Nn : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "q") = some (.val (.word (U + 216))) ∧ L.lookup (ofString "r") = some (.val (.word (U + 352))) ∧
    L.lookup (ofString "m") = some (.val (.word Mm)) ∧ L.lookup (ofString "n") = some (.val (.word Nn))

/-- Window frame of the actual `divmnu`: with the quotient/remainder buffers at `U + 216`, `U + 352` and digit counts
`1 ≤ n ≤ m ≤ 8`, every store lands in the 640-byte workspace at `U`. -/
theorem divmnu_window (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hN1 : 1 ≤ Nn.toNat)
    (hNM : Nn.toNat ≤ Mm.toNat) (hM8 : Mm.toNat ≤ 8) (hw : ¬ WS U w) :
    AQGD D B A w (fun x => x ≠ ofString "qr") (fun L _ _ => DVP U Mm Nn L) (fun _ _ _ => False)
      (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_divmnu) := by
  rw [divmnu_body_eq]
  unfold dmTop
  refine r_dec (LB := fun L => DVP U Mm Nn L ∧ L.lookup (ofString "i") = some (.val (.word 0)))
    (LQ' := fun _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ ⟨h1,h2,h3,h4⟩ ev
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact h1,by rw [lookup_update_ne' _ _ (by decide)]; exact h2,
      by rw [lookup_update_ne' _ _ (by decide)]; exact h3,by rw [lookup_update_ne' _ _ (by decide)]; exact h4⟩,
      lookup_update_eq' _ _ _⟩
  refine r_dec (LB := fun L => DV U Mm Nn 0 0 L) (LQ' := fun _ => False) _ _ _ (fun _ => rfl) ?_ ?_
    (fun _ _ _ h => h)
  · intro F s v _ ⟨⟨h1,h2,h3,h4⟩,hi⟩ ev
    simp [EV,evalHOLExact] at ev; subst ev
    refine ⟨?_,?_,?_,?_,⟨0,?_,by simp⟩,⟨0,lookup_update_eq' _ _ _,by simp⟩⟩ <;>
      (rw [lookup_update_ne' _ _ (by decide)]) <;> assumption
  exact aqgd_seq (r_ite _ (aqgd_conseq (dmBR1_aqgd hU hM8 hw 0 0) (fun _ _ _ h => h) (fun _ _ _ h => h.elim)
      (fun _ _ _ h => h)) aqgd_skip)
    (dmREST_aqgd hA hU hN1 hNM hM8 hw 0 0)

#print axioms divmnu_window
end dm
end InitECandidate.Runtime
