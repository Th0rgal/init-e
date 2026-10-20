import InitECandidate.Runtime.RecStoreGD
import InitECandidate.Runtime.VmFn_ec_set_affine
import InitECandidate.Runtime.VmFn_ec_set_infinity
import InitECandidate.Runtime.VmFn_secp_accel_modmul_p
import InitECandidate.Runtime.VmFn_secp_accel_modmul_n
import InitECandidate.Runtime.VmFn_fp_mul
import InitECandidate.Runtime.VmFn_fp_sqr
import InitECandidate.Runtime.VmFn_fn_mul
/-!
Window specs of the secp256k1 accelerator leaves: `ec_set_affine` / `ec_set_infinity` write only `[Pt, Pt + 96)`;
`secp_accel_modmul_p` / `_n` (and the tail calls `fp_mul`, `fp_sqr`, `fn_mul`) write only inside the accelerator
scratch `[Sc, Sc + 448)` (`secp_accel_scratch = Sc`, `ScrIs`) and return four-word values.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def esaBody : ProgHOL 64 :=
  (.seq (.store (.var .local (ofString "pt")) (.var .local (ofString "x"))) (.seq (.store (.op .add [(.var .local (ofString "pt")),(.const 32)]) (.var .local (ofString "y"))) (.seq (.store (.op .add [(.var .local (ofString "pt")),(.const 64)]) (.rstruct [(.const 1),(.const 0),(.const 0),(.const 0)])) (.return (.const 0)))))

theorem esaBody_eq : sourceFunctionBody Guest.guestFn_ec_set_affine = esaBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_ec_set_affine,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def esiBody : ProgHOL 64 :=
  (.seq (.store (.var .local (ofString "pt")) (.rstruct [(.const 1),(.const 0),(.const 0),(.const 0)])) (.seq (.store (.op .add [(.var .local (ofString "pt")),(.const 32)]) (.rstruct [(.const 1),(.const 0),(.const 0),(.const 0)])) (.seq (.store (.op .add [(.var .local (ofString "pt")),(.const 64)]) (.rstruct [(.const 0),(.const 0),(.const 0),(.const 0)])) (.return (.const 0)))))

theorem esiBody_eq : sourceFunctionBody Guest.guestFn_ec_set_infinity = esiBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_ec_set_infinity,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def mmpBody : ProgHOL 64 :=
  (.dec (ofString "base") .one (.op .add [(.var .global (ofString "secp_accel_scratch")),(.const 0)]) (.seq (.store (.op .add [(.var .local (ofString "base")),(.const 0)]) (.var .local (ofString "a"))) (.seq (.store (.op .add [(.var .local (ofString "base")),(.const 32)]) (.var .local (ofString "b"))) (.seq (.extCall (ofString "arith256mod") (.var .local (ofString "base")) (.const 0) (.var .local (ofString "base")) (.const 160)) (.return (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "base")),(.const 128)])))))))

theorem mmpBody_eq : sourceFunctionBody Guest.guestFn_secp_accel_modmul_p = mmpBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_secp_accel_modmul_p,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def mmnBody : ProgHOL 64 :=
  (.dec (ofString "base") .one (.op .add [(.var .global (ofString "secp_accel_scratch")),(.const 160)]) (.seq (.store (.op .add [(.var .local (ofString "base")),(.const 0)]) (.var .local (ofString "a"))) (.seq (.store (.op .add [(.var .local (ofString "base")),(.const 32)]) (.var .local (ofString "b"))) (.seq (.extCall (ofString "arith256mod") (.var .local (ofString "base")) (.const 0) (.var .local (ofString "base")) (.const 160)) (.return (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "base")),(.const 128)])))))))

theorem mmnBody_eq : sourceFunctionBody Guest.guestFn_secp_accel_modmul_n = mmnBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_secp_accel_modmul_n,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def fpmBody : ProgHOL 64 :=
  (.call none (ofString "secp_accel_modmul_p") [(.var .local (ofString "a")),(.var .local (ofString "b"))])

theorem fpmBody_eq : sourceFunctionBody Guest.guestFn_fp_mul = fpmBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_fp_mul,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def fnmBody : ProgHOL 64 :=
  (.call none (ofString "secp_accel_modmul_n") [(.var .local (ofString "a")),(.var .local (ofString "b"))])

theorem fnmBody_eq : sourceFunctionBody Guest.guestFn_fn_mul = fnmBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_fn_mul,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def fpsBody : ProgHOL 64 :=
  (.call none (ofString "secp_accel_modmul_p") [(.var .local (ofString "a")),(.var .local (ofString "a"))])

theorem fpsBody_eq : sourceFunctionBody Guest.guestFn_fp_sqr = fpsBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_fp_sqr,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl


theorem u4_of_vals (m0 m1 m2 m3 : HolWordLab 64) : U4V (.rStruct [.val m0,.val m1,.val m2,.val m3]) := by
  cases m0; cases m1; cases m2; cases m3; exact ⟨_,_,_,_,rfl⟩

theorem ev_load_u4 {F : Type} (s : PanSemStateFiniteExact 64 F) (a : ExpHOL 64) (x : ValueHOL 64)
    (ev : EV s (.load (.comb [.one,.one,.one,.one]) a) = some x) : U4V x := by
  simp only [EV,evalHOLExact] at ev
  split at ev
  · split at ev
    · rename_i addr _
      simp only [memLoadHOLExact,memLoadsHOLExact] at ev
      split_ifs at ev <;> simp at ev
      subst ev
      exact u4_of_vals _ _ _ _
    · cases ev
  · cases ev

theorem ofNat_add_add (Dd : BitVec 64) (a b : Nat) :
    Dd + BitVec.ofNat 64 a + BitVec.ofNat 64 b = Dd + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc,BitVec.ofNat_add]

/-- The words of a four-word store at offset `o` of a window avoiding `w`. -/
theorem st4_out {Dd w : BitVec 64} {N : Nat} (out : ¬ MWin Dd N w) (o : Nat) (ho : o + 32 ≤ N) :
    ∀ j : Nat, j < 4 → w ≠ Dd + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * j) := fun j hj e =>
  out ⟨o + 8 * j,by omega,Or.inl (by rw [e,ofNat_add_add])⟩

/-- `secp_accel_scratch` holds `Sc`. -/
def ScrIs (Sc : BitVec 64) (G : GA) : Prop := G.lookup (ofString "secp_accel_scratch") = some (.val (.word Sc))

/-- A local holding a four-word value. -/
def LU4 (x : MlS) (L : GA) : Prop := ∃ v, L.lookup x = some v ∧ U4V v

theorem lu4_upd {x n : MlS} (h : x ≠ n) (L : GA) (v : ValueHOL 64) (hx : LU4 x L) : LU4 x (L.update (n,v)) :=
  let ⟨u,hu,uu⟩ := hx; ⟨u,by rw [lookup_update_ne' _ _ h]; exact hu,uu⟩

theorem ev_var_u4 {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (h : LU4 x s.locals) :
    ∀ v, EV s (.var .local x) = some v → (flattenHOL v).length = 4 := fun v ev => by
  obtain ⟨u,hu,uu⟩ := h
  simp [EV,evalHOLExact,hu] at ev; subst ev; exact u4v_len uu

theorem ev_const4_len {F : Type} (s : PanSemStateFiniteExact 64 F) (a b c d : BitVec 64) :
    ∀ v, EV s (.rstruct [.const a,.const b,.const c,.const d]) = some v → (flattenHOL v).length = 4 := fun v ev => by
  simp [EV,evalHOLExact,evalListHOLExact] at ev; subst ev; simp [flattenHOL]

section leaf
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}

/-- `ec_set_affine(pt, x, y)` writes only `[Pt, Pt + 96)`. -/
theorem ecSetAffine_wn (Pt : BitVec 64) (out : ¬ MWin Pt 96 w) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ LU4 (ofString "x") L ∧ LU4 (ofString "y") L)
      (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_ec_set_affine) := by
  rw [esaBody_eq]; unfold esaBody
  let P := fun (L : GA) (_ : GA) => L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ LU4 (ofString "x") L ∧
    LU4 (ofString "y") L
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ fun s _ pre => ⟨Pt,4,by simp [EV,evalHOLExact,pre.1],
    ev_var_u4 s _ pre.2.1,fun j hj => by simpa using st4_out out 0 (by omega) j hj,pre⟩) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ fun s _ pre => ⟨Pt + 32#64,4,
    by simp [EV,evalHOLExact,evalListHOLExact,pre.1,wordOpHOL,wordOp,valueIsWord,valueWord],
    ev_var_u4 s _ pre.2.2,st4_out out 32 (by omega),pre⟩) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ fun s _ pre => ⟨Pt + 64#64,4,
    by simp [EV,evalHOLExact,evalListHOLExact,pre.1,wordOpHOL,wordOp,valueIsWord,valueWord],
    ev_const4_len s _ _ _ _,st4_out out 64 (by omega),pre⟩) ?_
  exact aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)

/-- `ec_set_infinity(pt)` writes only `[Pt, Pt + 96)`. -/
theorem ecSetInfinity_wn (Pt : BitVec 64) (out : ¬ MWin Pt 96 w) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "pt") = some (.val (.word Pt)))
      (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_ec_set_infinity) := by
  rw [esiBody_eq]; unfold esiBody
  let P := fun (L : GA) (_ : GA) => L.lookup (ofString "pt") = some (.val (.word Pt))
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ fun s _ pre => ⟨Pt,4,by simp [EV,evalHOLExact,(show s.locals.lookup (ofString "pt") = some (.val (.word Pt)) from pre)],
    ev_const4_len s _ _ _ _,fun j hj => by simpa using st4_out out 0 (by omega) j hj,pre⟩) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ fun s _ pre => ⟨Pt + 32#64,4,
    by simp [EV,evalHOLExact,evalListHOLExact,(show s.locals.lookup (ofString "pt") = some (.val (.word Pt)) from pre),wordOpHOL,wordOp,valueIsWord,valueWord],
    ev_const4_len s _ _ _ _,st4_out out 32 (by omega),pre⟩) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ fun s _ pre => ⟨Pt + 64#64,4,
    by simp [EV,evalHOLExact,evalListHOLExact,(show s.locals.lookup (ofString "pt") = some (.val (.word Pt)) from pre),wordOpHOL,wordOp,valueIsWord,valueWord],
    ev_const4_len s _ _ _ _,st4_out out 64 (by omega),pre⟩) ?_
  exact aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)

#print axioms ecSetInfinity_wn

/-- `secp_accel_modmul_p(a, b)` / `secp_accel_modmul_n(a, b)`: writes only `[Sc + off, Sc + off + 160)` inside the
scratch `[Sc, Sc + 448)`; returns a four-word value. -/
theorem modmul_wn (Sc : BitVec 64) (out : ¬ MWin Sc 448 w) (off : Nat) (hoff : off + 160 ≤ 448)
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "base") .one (.op .add [(.var .global (ofString "secp_accel_scratch")),
      (.const (BitVec.ofNat 64 off))]) (.seq (.store (.op .add [(.var .local (ofString "base")),(.const 0)])
      (.var .local (ofString "a"))) (.seq (.store (.op .add [(.var .local (ofString "base")),(.const 32)])
      (.var .local (ofString "b"))) (.seq (.extCall (ofString "arith256mod") (.var .local (ofString "base")) (.const 0)
      (.var .local (ofString "base")) (.const 160)) (.return (.load (.comb [.one,.one,.one,.one])
      (.op .add [(.var .local (ofString "base")),(.const 128)]))))))) :
    AQGD D B A w (fun _ => False) (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G) body := by
  subst hbody
  let P := fun (L : GA) (G : GA) => ((LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧
    L.lookup (ofString "base") = some (.val (.word (Sc + BitVec.ofNat 64 off)))) ∧ ScrIs Sc G
  refine aqgd_dec (Pb := fun L _ G => P L G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H _ hG ⟨⟨ha,hb⟩,hsc⟩ _ ev _
    unfold GIs at hG; subst hG
    have hsc' : s.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word Sc)) := hsc
    simp [EV,evalHOLExact,evalListHOLExact,hsc',wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    exact ⟨⟨⟨lu4_upd (by decide) _ _ ha,lu4_upd (by decide) _ _ hb⟩,lookup_update_eq' _ _ _⟩,hsc⟩
  have hbase : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s.locals s.globals →
      s.locals.lookup (ofString "base") = some (.val (.word (Sc + BitVec.ofNat 64 off))) := fun s pre => pre.1.2
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ fun s _ pre => ⟨Sc + BitVec.ofNat 64 off,4,
    by simp [EV,evalHOLExact,evalListHOLExact,hbase s pre,wordOpHOL,wordOp,valueIsWord,valueWord],
    ev_var_u4 s _ pre.1.1.1,st4_out out off (by omega),pre⟩) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ fun s _ pre => ⟨Sc + BitVec.ofNat 64 (off + 32),4,
    by simp [EV,evalHOLExact,evalListHOLExact,hbase s pre,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc,
      BitVec.ofNat_add],
    ev_var_u4 s _ pre.1.1.2,st4_out out (off + 32) (by omega),pre⟩) ?_
  refine aqgd_seq (aqgd_extCall (LP := P) (LQ := P) _ _ _ _ _ fun s _ pre => ⟨Sc + BitVec.ofNat 64 off,160#64,
    by simp [EV,evalHOLExact,hbase s pre],by simp [EV,evalHOLExact],fun j hj e => out ⟨off + j,by
      have : (160#64).toNat = 160 := rfl
      omega,Or.inr (by rw [e,ofNat_add_add])⟩,pre⟩) ?_
  exact aqgd_return _ (fun s v _ _ _ pre _ ev => ⟨ev_load_u4 s _ v ev,pre.2⟩)

theorem modmulP_wn (Sc : BitVec 64) (out : ¬ MWin Sc 448 w) :
    AQGD D B A w (fun _ => False) (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G) (sourceFunctionBody Guest.guestFn_secp_accel_modmul_p) := by
  rw [mmpBody_eq]
  exact modmul_wn Sc out 0 (by decide) _ rfl

theorem modmulN_wn (Sc : BitVec 64) (out : ¬ MWin Sc 448 w) :
    AQGD D B A w (fun _ => False) (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G) (sourceFunctionBody Guest.guestFn_secp_accel_modmul_n) := by
  rw [mmnBody_eq]
  exact modmul_wn Sc out 160 (by decide) _ rfl

#print axioms modmulN_wn

/-- Tail call `f(a, b)` / `f(a, a)` of a modular multiplier. -/
theorem modmulTail_wn (Sc : BitVec 64) (out : ¬ MWin Sc 448 w) (callee0 : MlS) (body0 : ProgHOL 64)
    (inst : originalRuntimeCode.lookup callee0 = some ([(ofString "a",.comb [.one,.one,.one,.one]),
      (ofString "b",.comb [.one,.one,.one,.one])],body0,.comb [.one,.one,.one,.one]))
    (hb0 : AQGD D B A w (fun _ => False) (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G) body0) (x y : MlS) :
    AQGD D B A w (fun _ => False) (fun L _ G => (LU4 x L ∧ LU4 y L) ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G)
      (.call none callee0 [.var .local x,.var .local y]) :=
  aqgd_tailCallSpecS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
    (RRe := fun _ _ _ r _ G => U4V r ∧ ScrIs Sc G) _ _ _ _ _ inst (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ => hb0)
    (fun s values callee rs _ H hG ⟨⟨⟨va,ha,ua⟩,⟨vb,hb,ub⟩⟩,hsc⟩ _ args lookup => by
      unfold GIs at hG; subst hG
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,ha,hb] at args
      subst args
      have e := callee_eq inst lookup
      exact ⟨⟨⟨va,by rw [e]; simp (config := {decide := true}),ua⟩,⟨vb,by rw [e]; simp (config := {decide := true}),ub⟩⟩,hsc⟩)
    (fun _ _ _ _ _ _ _ h => h)

theorem fpMul_wn (Sc : BitVec 64) (out : ¬ MWin Sc 448 w) :
    AQGD D B A w (fun _ => False) (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G) (sourceFunctionBody Guest.guestFn_fp_mul) := by
  rw [fpmBody_eq]; unfold fpmBody
  exact modmulTail_wn Sc out _ _ vmLookup_secp_accel_modmul_p (modmulP_wn Sc out) _ _

theorem fnMul_wn (Sc : BitVec 64) (out : ¬ MWin Sc 448 w) :
    AQGD D B A w (fun _ => False) (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G) (sourceFunctionBody Guest.guestFn_fn_mul) := by
  rw [fnmBody_eq]; unfold fnmBody
  exact modmulTail_wn Sc out _ _ vmLookup_secp_accel_modmul_n (modmulN_wn Sc out) _ _

theorem fpSqr_wn (Sc : BitVec 64) (out : ¬ MWin Sc 448 w) :
    AQGD D B A w (fun _ => False) (fun L _ G => LU4 (ofString "a") L ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G) (sourceFunctionBody Guest.guestFn_fp_sqr) := by
  rw [fpsBody_eq]; unfold fpsBody
  exact aqgd_conseq (modmulTail_wn Sc out _ _ vmLookup_secp_accel_modmul_p (modmulP_wn Sc out) _ _)
    (fun _ _ _ ⟨h,g⟩ => ⟨⟨h,h⟩,g⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms fpSqr_wn
end leaf
end InitECandidate.Runtime
