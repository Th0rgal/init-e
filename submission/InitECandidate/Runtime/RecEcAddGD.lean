import InitECandidate.Runtime.RecEcGD
import InitECandidate.Runtime.OriginalSecpInitCode
import InitECandidate.Runtime.VmFn_fp_add
/-!
`secp256k1_init` is a no-op once the accelerator scratch is set (`Sc ≠ 0`, set by `main` at startup), and the window
spec of the actual `ec_add_affine(pt, ax, ay)` (split into the `samex` branch, the accelerator add block at
`[Sc + 320, Sc + 448)`, and the middle part).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def sinitBody : ProgHOL 64 :=
  (.seq (.ite (.cmp .notEqual (.var .global (ofString "secp_accel_scratch")) (.const 0)) (.return (.const 0)) .skip) (.seq (.call (some ((some (.global,ofString "secp_accel_scratch")),none)) (ofString "alloc") [(.op .add [(.panop .mul [(.const 2),(.const 160)]),(.const 128)])]) (.seq (.call (some (none,none)) (ofString "secp_accel_init_block") [(.op .add [(.var .global (ofString "secp_accel_scratch")),(.const 0)]),(.rstruct [(.const 18446744069414583343),(.const 18446744073709551615),(.const 18446744073709551615),(.const 18446744073709551615)])]) (.seq (.call (some (none,none)) (ofString "secp_accel_init_block") [(.op .add [(.var .global (ofString "secp_accel_scratch")),(.const 160)]),(.rstruct [(.const 13822214165235122497),(.const 13451932020343611451),(.const 18446744073709551614),(.const 18446744073709551615)])]) (.return (.const 0))))))

theorem sinitBody_eq : sourceFunctionBody Guest.guestFn_secp256k1_init = sinitBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_secp256k1_init,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def eaaAdd : ProgHOL 64 :=
  (.seq (.call (some (none,none)) (ofString "secp256k1_init") []) (.dec (ofString "blk") .one (.op .add [(.var .global (ofString "secp_accel_scratch")),(.panop .mul [(.const 2),(.const 160)])]) (.seq (.store (.op .add [(.var .local (ofString "blk")),(.const 0)]) (.var .local (ofString "x1"))) (.seq (.store (.op .add [(.var .local (ofString "blk")),(.const 0),(.const 32)]) (.var .local (ofString "y1"))) (.seq (.store (.op .add [(.var .local (ofString "blk")),(.const 64)]) (.var .local (ofString "ax"))) (.seq (.store (.op .add [(.var .local (ofString "blk")),(.const 64),(.const 32)]) (.var .local (ofString "ay"))) (.seq (.extCall (ofString "secpadd") (.var .local (ofString "blk")) (.const 0) (.var .local (ofString "blk")) (.const 128)) (.seq (.store (.var .local (ofString "pt")) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "blk")),(.const 0)]))) (.seq (.store (.op .add [(.var .local (ofString "pt")),(.const 32)]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "blk")),(.const 0),(.const 32)]))) (.seq (.store (.op .add [(.var .local (ofString "pt")),(.const 64)]) (.rstruct [(.const 1),(.const 0),(.const 0),(.const 0)])) (.return (.const 0))))))))))))

def eaaSame : ProgHOL 64 :=
  (.decCall (ofString "ysum") (.comb [.one,.one,.one,.one]) (ofString "fp_add") [(.var .local (ofString "y1")),(.var .local (ofString "ay"))] (.decCall (ofString "ysz") .one (ofString "u256_is_zero") [(.var .local (ofString "ysum"))] (.seq (.ite (.cmp .equal (.var .local (ofString "ysz")) (.const 1)) (.seq (.call (some (none,none)) (ofString "ec_set_infinity") [(.var .local (ofString "pt"))]) (.return (.const 0))) .skip) (.seq (.call (some (none,none)) (ofString "ec_double") [(.var .local (ofString "pt"))]) (.return (.const 0))))))

def eaaMid : ProgHOL 64 :=
  (.dec (ofString "x1") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.var .local (ofString "pt"))) (.dec (ofString "y1") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pt")),(.const 32)])) (.decCall (ofString "samex") .one (ofString "u256_eq") [(.var .local (ofString "x1")),(.var .local (ofString "ax"))] (.seq (.ite (.cmp .equal (.var .local (ofString "samex")) (.const 1)) eaaSame .skip) eaaAdd))))

def eaaTop : ProgHOL 64 :=
  (.dec (ofString "z1") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pt")),(.const 64)])) (.decCall (ofString "zz") .one (ofString "u256_is_zero") [(.var .local (ofString "z1"))] (.seq (.ite (.cmp .equal (.var .local (ofString "zz")) (.const 1)) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.var .local (ofString "pt")),(.var .local (ofString "ax")),(.var .local (ofString "ay"))]) (.return (.const 0))) .skip) (.decCall (ofString "affine") .one (ofString "u256_eq") [(.var .local (ofString "z1")),(.rstruct [(.const 1),(.const 0),(.const 0),(.const 0)])] (.seq (.ite (.cmp .equal (.var .local (ofString "affine")) (.const 0)) (.call (some (none,none)) (ofString "secp_accel_normalize") [(.var .local (ofString "pt"))]) .skip) eaaMid)))))

theorem eaaTop_eq : sourceFunctionBody Guest.guestFn_ec_add_affine = eaaTop := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_ec_add_affine,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- Locals of `ec_add_affine`: the point and the four-word coordinates. -/
def EA0 (Pt : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ LU4 (ofString "ax") L ∧ LU4 (ofString "ay") L

def EA1 (Pt : BitVec 64) (L : GA) : Prop := (EA0 Pt L ∧ LU4 (ofString "x1") L) ∧ LU4 (ofString "y1") L

theorem ea0u {Pt : BitVec 64} (n : MlS) (h1 : ofString "pt" ≠ n) (h2 : ofString "ax" ≠ n) (h3 : ofString "ay" ≠ n)
    (L : GA) (v : ValueHOL 64) (h : EA0 Pt L) : EA0 Pt (L.update (n,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,lu4_upd h2 _ _ h.2.1,lu4_upd h3 _ _ h.2.2⟩

theorem ea1u {Pt : BitVec 64} (n : MlS) (h1 : ofString "pt" ≠ n) (h2 : ofString "ax" ≠ n) (h3 : ofString "ay" ≠ n)
    (h4 : ofString "x1" ≠ n) (h5 : ofString "y1" ≠ n) (L : GA) (v : ValueHOL 64) (h : EA1 Pt L) :
    EA1 Pt (L.update (n,v)) :=
  ⟨⟨ea0u n h1 h2 h3 L v h.1.1,lu4_upd h4 _ _ h.1.2⟩,lu4_upd h5 _ _ h.2⟩

theorem ea0_pt {Pt : BitVec 64} {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EA0 Pt s.locals) :
    EV s (.var .local (ofString "pt")) = some (.val (.word Pt)) := by simp [EV,evalHOLExact,h.1]

section ea
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {A : GA → Prop}

/-- With the accelerator scratch already set (`Sc ≠ 0`), the actual `secp256k1_init()` returns at once. -/
theorem secpInit_wn (Lo Sc : BitVec 64) (hSc0 : Sc ≠ 0) :
    AQGD D B A w (fun _ => False) (fun _ _ G => RG Lo Sc G) (fun _ _ _ => True) (fun _ _ G => RG Lo Sc G)
      (sourceFunctionBody Guest.guestFn_secp256k1_init) := by
  rw [sinitBody_eq]; unfold sinitBody
  refine aqgd_seq (Q := fun _ _ _ => False) (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => False) _ ?_
    (aqgd_return _ (fun _ _ _ _ _ ⟨rg,_⟩ _ _ => rg)) (aqgd_conseq aqgd_skip (fun _ _ _ h => h.2) (fun _ _ _ h => h)
      (fun _ _ _ h => h))) aqgd_false
  intro F s x H _ hG ⟨_,hsc⟩ _ ev
  unfold GIs at hG; subst hG
  have hsc' : s.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word Sc)) := hsc
  simp [EV,evalHOLExact,hsc',Compiler.Encoders.Asm.wordCmpHOL] at ev
  refine ⟨fun _ => trivial,fun hx => ?_⟩
  subst hx
  by_cases h : Sc = 0#64
  · exact hSc0 h
  · rw [if_neg h] at ev; exact absurd ev (by decide)

#print axioms secpInit_wn

theorem retRG {LP : GA → Prop} (Lo Sc : BitVec 64) (e : ExpHOL 64) {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ RG Lo Sc G) Q
      (fun _ _ G => RG Lo Sc G) (.return e) :=
  aqgd_return _ (fun _ _ _ _ _ ⟨_,rg⟩ _ _ => rg)

/-- The `samex` branch of `ec_add_affine`: `fp_add`, `u256_is_zero`, `ec_set_infinity` or `ec_double` at `Pt`. -/
theorem eaaSame_wn (Lo Sc Pt : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (oP : ¬ MWin Pt 96 w)
    {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => EA1 Pt L ∧ RG Lo Sc G) Q
      (fun _ _ G => RG Lo Sc G) eaaSame := by
  unfold eaaSame
  refine rdecMF (LP' := EA1 Pt) (ofString "ysum") _ _ _ _ _ _ vmLookup_fp_add
    (memoryFrame_of_good vmLookup_fp_add (by decide) (by decide)) (by body_check Guest.guestFn_fp_add)
    (by body_check Guest.guestFn_fp_add)
    (fun L v a1 => ea1u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ a1) ?_
  refine rdecMF (LP' := EA1 Pt) (ofString "ysz") _ _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero)
    (fun L v a1 => ea1u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ a1) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (rcallK (GP := RG Lo Sc) (LP := EA1 Pt)
    (fun L => L.lookup (ofString "pt") = some (.val (.word Pt))) _ _ _ _ _ vmLookup_ec_set_infinity
    (ecSetInfRG Lo Sc Pt oP)
    (fun s values callee rs a1 args lookup => entry_pt vmLookup_ec_set_infinity s _ Pt (ea0_pt s a1.1.1) args lookup))
    (retRG Lo Sc _)) aqgd_skip) ?_
  exact aqgd_seq (rcallK (GP := RG Lo Sc) (LP := EA1 Pt) (Rv := fun _ => True)
    (fun L => L.lookup (ofString "pt") = some (.val (.word Pt))) _ _ _ _ _ originalRuntimeCode_ecDouble_lookup
    (aqgd_conseq (ecDouble_wn Lo Sc Pt hw out oP) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs a1 args lookup => entry_pt originalRuntimeCode_ecDouble_lookup s _ Pt (ea0_pt s a1.1.1)
      args lookup)) (retRG Lo Sc _)

#print axioms eaaSame_wn

/-- The accelerator add block of `ec_add_affine`: `secp256k1_init` (no-op), the block `[Sc + 320, Sc + 448)`, `@secpadd`,
the result stored at `Pt`. -/
theorem eaaAdd_wn (Lo Sc Pt : BitVec 64) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0) (oP : ¬ MWin Pt 96 w)
    {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => EA1 Pt L ∧ RG Lo Sc G) Q
      (fun _ _ G => RG Lo Sc G) eaaAdd := by
  unfold eaaAdd
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := EA1 Pt) (Rv := fun _ => True) (fun _ => True) _ _ _ _ _
    originalRuntimeCode_secp256k1Init_lookup (aqgd_conseq (secpInit_wn Lo Sc hSc0) (fun _ _ _ h => h.2)
      (fun _ _ _ h => h) (fun _ _ _ h => ⟨trivial,h⟩)) (fun _ _ _ _ _ _ _ => trivial)) ?_
  let EB := fun L : GA => EA1 Pt L ∧ L.lookup (ofString "blk") = some (.val (.word (Sc + 320#64)))
  refine aqgd_dec (Pb := fun L _ G => EB L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v H _ hG ⟨a1,rg⟩ _ ev _ => by
      unfold GIs at hG; subst hG
      have hsc : s.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word Sc)) := rg.2
      simp [EV,evalHOLExact,evalListHOLExact,hsc,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL] at ev; subst ev
      exact ⟨⟨ea1u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ a1,lookup_update_eq' _ _ _⟩,rg⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  have hb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), EB s.locals →
      s.locals.lookup (ofString "blk") = some (.val (.word (Sc + 320#64))) := fun _ h => h.2
  have hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), EB s.locals →
      s.locals.lookup (ofString "pt") = some (.val (.word Pt)) := fun _ h => h.1.1.1.1
  let P := fun (L : GA) (G : GA) => EB L ∧ RG Lo Sc G
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ (fun s _ pre => ⟨Sc + 320#64,4,
    by simp [EV,evalHOLExact,evalListHOLExact,hb s pre.1,wordOpHOL,wordOp,valueIsWord,valueWord],
    ev_var_u4 s _ pre.1.1.1.2,st4_out out 320 (by omega),pre⟩)) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ (fun s _ pre => ⟨Sc + BitVec.ofNat 64 352,4,
    by simp [EV,evalHOLExact,evalListHOLExact,hb s pre.1,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc],
    ev_var_u4 s _ pre.1.1.2,st4_out out 352 (by omega),pre⟩)) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ (fun s _ pre => ⟨Sc + BitVec.ofNat 64 384,4,
    by simp [EV,evalHOLExact,evalListHOLExact,hb s pre.1,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc],
    ev_var_u4 s _ pre.1.1.1.1.2.1,st4_out out 384 (by omega),pre⟩)) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ (fun s _ pre => ⟨Sc + BitVec.ofNat 64 416,4,
    by simp [EV,evalHOLExact,evalListHOLExact,hb s pre.1,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc],
    ev_var_u4 s _ pre.1.1.1.1.2.2,st4_out out 416 (by omega),pre⟩)) ?_
  refine aqgd_seq (aqgd_extCall (LP := P) (LQ := P) _ _ _ _ _ (fun s _ pre => ⟨Sc + 320#64,128#64,
    by simp [EV,evalHOLExact,hb s pre.1],by simp [EV,evalHOLExact],fun j hj e => out ⟨320 + j,by
      have : (128#64).toNat = 128 := rfl
      omega,Or.inr (by rw [e,ofNat_add_add])⟩,pre⟩)) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ (fun s _ pre => ⟨Pt,4,by simp [EV,evalHOLExact,hp s pre.1],
    fun x ev => u4v_len (ev_load_u4 s _ x ev),fun j hj => by simpa using st4_out oP 0 (by omega) j hj,pre⟩)) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ (fun s _ pre => ⟨Pt + 32#64,4,
    by simp [EV,evalHOLExact,evalListHOLExact,hp s pre.1,wordOpHOL,wordOp,valueIsWord,valueWord],
    fun x ev => u4v_len (ev_load_u4 s _ x ev),st4_out oP 32 (by omega),pre⟩)) ?_
  refine aqgd_seq (aqgd_storeK (LP := P) (LQ := P) _ _ (fun s _ pre => ⟨Pt + 64#64,4,
    by simp [EV,evalHOLExact,evalListHOLExact,hp s pre.1,wordOpHOL,wordOp,valueIsWord,valueWord],
    ev_const4_len s _ _ _ _,st4_out oP 64 (by omega),pre⟩)) ?_
  exact retRG Lo Sc _

#print axioms eaaAdd_wn

theorem eaaMid_wn (Lo Sc Pt : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0)
    (oP : ¬ MWin Pt 96 w) {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => EA0 Pt L ∧ RG Lo Sc G) Q
      (fun _ _ G => RG Lo Sc G) eaaMid := by
  unfold eaaMid
  refine aqgd_dec (Pb := fun L _ G => (EA0 Pt L ∧ LU4 (ofString "x1") L) ∧ RG Lo Sc G) (Qb := fun _ _ _ => False)
    _ _ _ (fun h => h.elim) (fun s v H _ hG ⟨a0,rg⟩ _ ev _ => by
      unfold GIs at hG; subst hG
      exact ⟨⟨ea0u _ (by decide) (by decide) (by decide) _ _ a0,lu4_ld s _ _ v ev⟩,rg⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  refine aqgd_dec (Pb := fun L _ G => EA1 Pt L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False)
    _ _ _ (fun h => h.elim) (fun s v H _ hG ⟨⟨a0,hx⟩,rg⟩ _ ev _ => by
      unfold GIs at hG; subst hG
      exact ⟨⟨⟨ea0u _ (by decide) (by decide) (by decide) _ _ a0,lu4_upd (by decide) _ _ hx⟩,lu4_ld s _ _ v ev⟩,rg⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  refine rdecMF (LP' := EA1 Pt) (ofString "samex") _ _ _ _ _ _ vmLookup_u256_eq
    (memoryFrame_of_good vmLookup_u256_eq (by decide) (by decide)) (by body_check Guest.guestFn_u256_eq)
    (by body_check Guest.guestFn_u256_eq)
    (fun L v a1 => ea1u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ a1) ?_
  exact aqgd_seq (aqgd_iteT _ (eaaSame_wn Lo Sc Pt hw out oP) aqgd_skip) (eaaAdd_wn Lo Sc Pt out hSc0 oP)

/-- The actual `ec_add_affine(pt, ax, ay)`: writes only `[Pt, Pt + 96)`, the accelerator scratch (including the add
block `[Sc + 320, Sc + 448)`) and released heap; keeps `RG` (the scratch already set, `Sc ≠ 0`). -/
theorem ecAddAffine_wn (Lo Sc Pt : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0)
    (oP : ¬ MWin Pt 96 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => EA0 Pt L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_ec_add_affine) := by
  rw [eaaTop_eq]; unfold eaaTop
  refine aqgd_dec (Pb := fun L _ G => EA0 Pt L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v H _ hG ⟨a0,rg⟩ _ _ _ => by
      unfold GIs at hG; subst hG; exact ⟨ea0u _ (by decide) (by decide) (by decide) _ _ a0,rg⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  refine rdecMF (LP' := EA0 Pt) (ofString "zz") _ _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero) (fun L v a0 => ea0u _ (by decide) (by decide) (by decide) _ _ a0) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (rcallK (GP := RG Lo Sc) (LP := EA0 Pt)
    (fun L => L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ LU4 (ofString "x") L ∧ LU4 (ofString "y") L)
    _ _ _ _ _ vmLookup_ec_set_affine (ecSetAffineRG Lo Sc Pt oP)
    (fun s values callee rs a0 args lookup => entry_esa s _ Pt (ea0_pt s a0) _ _ (ev_var_u4v s _ a0.2.1)
      (ev_var_u4v s _ a0.2.2) args lookup)) (retRG Lo Sc _)) aqgd_skip) ?_
  refine rdecMF (LP' := EA0 Pt) (ofString "affine") _ _ _ _ _ _ vmLookup_u256_eq
    (memoryFrame_of_good vmLookup_u256_eq (by decide) (by decide)) (by body_check Guest.guestFn_u256_eq)
    (by body_check Guest.guestFn_u256_eq) (fun L v a0 => ea0u _ (by decide) (by decide) (by decide) _ _ a0) ?_
  exact aqgd_seq (aqgd_iteT _ (rcallK (GP := RG Lo Sc) (LP := EA0 Pt) (Rv := fun _ => True)
    (fun L => L.lookup (ofString "pt") = some (.val (.word Pt))) _ _ _ _ _ originalRuntimeCode_secpAccelNormalize_lookup
    (aqgd_conseq (normalize_wn Lo Sc Pt hw out oP) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs a0 args lookup =>
      entry_pt originalRuntimeCode_secpAccelNormalize_lookup s _ Pt (ea0_pt s a0) args lookup)) aqgd_skip)
    (eaaMid_wn Lo Sc Pt hw out hSc0 oP)

#print axioms ecAddAffine_wn
end ea
end InitECandidate.Runtime
