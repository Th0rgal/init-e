import InitECandidate.Runtime.RecSecpMidGD
import InitECandidate.Runtime.VmFn_u256_is_zero
import InitECandidate.Runtime.VmFn_u256_eq
import InitECandidate.Runtime.VmFn_ec_set_infinity
/-!
Window specs of the actual `ec_double(pt)` and `ec_to_affine(pt)`: they write only `[Pt, Pt + 96)`, the accelerator
scratch and released heap, and keep `RG`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def etaBody : ProgHOL 64 :=
  (.dec (ofString "z") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pt")),(.const 64)])) (.decCall (ofString "zz") .one (ofString "u256_is_zero") [(.var .local (ofString "z"))] (.seq (.ite (.cmp .equal (.var .local (ofString "zz")) (.const 1)) (.return (.const 0)) .skip) (.decCall (ofString "zi") (.comb [.one,.one,.one,.one]) (ofString "fp_inv") [(.var .local (ofString "z"))] (.decCall (ofString "zi2") (.comb [.one,.one,.one,.one]) (ofString "fp_sqr") [(.var .local (ofString "zi"))] (.decCall (ofString "zi3") (.comb [.one,.one,.one,.one]) (ofString "fp_mul") [(.var .local (ofString "zi2")),(.var .local (ofString "zi"))] (.dec (ofString "x") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.var .local (ofString "pt"))) (.dec (ofString "y") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pt")),(.const 32)])) (.seq (.call (some ((some (.local,ofString "x")),none)) (ofString "fp_mul") [(.var .local (ofString "x")),(.var .local (ofString "zi2"))]) (.seq (.call (some ((some (.local,ofString "y")),none)) (ofString "fp_mul") [(.var .local (ofString "y")),(.var .local (ofString "zi3"))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.var .local (ofString "pt")),(.var .local (ofString "x")),(.var .local (ofString "y"))]) (.return (.const 1)))))))))))))

theorem etaBody_eq : sourceFunctionBody Guest.guestFn_ec_to_affine = etaBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_ec_to_affine,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def edbBody : ProgHOL 64 :=
  (.dec (ofString "z") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pt")),(.const 64)])) (.decCall (ofString "zz") .one (ofString "u256_is_zero") [(.var .local (ofString "z"))] (.seq (.ite (.cmp .equal (.var .local (ofString "zz")) (.const 1)) (.return (.const 0)) .skip) (.dec (ofString "y") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pt")),(.const 32)])) (.decCall (ofString "yz") .one (ofString "u256_is_zero") [(.var .local (ofString "y"))] (.seq (.ite (.cmp .equal (.var .local (ofString "yz")) (.const 1)) (.seq (.call (some (none,none)) (ofString "ec_set_infinity") [(.var .local (ofString "pt"))]) (.return (.const 0))) .skip) (.decCall (ofString "affine") .one (ofString "u256_eq") [(.var .local (ofString "z")),(.rstruct [(.const 1),(.const 0),(.const 0),(.const 0)])] (.seq (.ite (.cmp .equal (.var .local (ofString "affine")) (.const 0)) (.call (some (none,none)) (ofString "secp_accel_normalize") [(.var .local (ofString "pt"))]) .skip) (.seq (.extCall (ofString "secpdbl") (.var .local (ofString "pt")) (.const 0) (.var .local (ofString "pt")) (.const 64)) (.seq (.store (.op .add [(.var .local (ofString "pt")),(.const 64)]) (.rstruct [(.const 1),(.const 0),(.const 0),(.const 0)])) (.return (.const 0))))))))))))

theorem edbBody_eq : sourceFunctionBody Guest.guestFn_ec_double = edbBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_ec_double,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl


section ed
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `var x = f(args); cont` for a memory-and-globals-keeping callee. -/
theorem rdecMF {GP LP LP' : GA → Prop} (x f : MlS) (args : List (ExpHOL 64)) {cont : ProgHOL 64} (sh : ShapeHOL)
    (params : List (MlS × ShapeHOL)) (body0 : ProgHOL 64) (rs0 : ShapeHOL)
    (inst : originalRuntimeCode.lookup f = some (params,body0,rs0)) (mf : MemoryFrame body0)
    (nb : noTopBreak body0 = true) (nc : noTopContinue body0 = true)
    (hup : ∀ L v, LP L → LP' (L.update (x,v)))
    (hc : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP' L ∧ GP G)
      (fun _ _ _ => False) RR cont) {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ GP G) Q RR
      (.decCall x sh f args cont) :=
  aqgd_decCall_mfF _ _ _ _ _ _ _ inst mf nb nc (fun L M G v ⟨lp,g⟩ => ⟨hup L v lp,g⟩) hc
    (fun _ _ _ _ _ _ _ h => h.elim)

theorem ecSetInfRG (Lo Sc Pt : BitVec 64) (out : ¬ MWin Pt 96 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => True ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_ec_set_infinity) :=
  aqgd_conseq (aqgd_keepGI (GI := RG Lo Sc) (keepsGA_of_installed vmLookup_ec_set_infinity (by decide))
    (ecSetInfinity_wn Pt out)) (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

theorem entry_pt {f : MlS} {bd : ProgHOL 64}
    (inst : originalRuntimeCode.lookup f = some ([(ofString "pt",.one)],bd,.one)) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (Pt : BitVec 64) (h : EV s e = some (.val (.word Pt)))
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    callee.lookup (ofString "pt") = some (.val (.word Pt)) := by
  obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
  rw [h] at ex; simp only [Option.some.injEq] at ex; subst ex
  rw [pan_single_word_lookup _ _ _ _ _ inst] at lookup
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup
  obtain ⟨_,rfl,_⟩ := lookup
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms entry_pt

/-- The actual `ec_double(pt)`: writes only `[Pt, Pt + 96)` (directly and through `ec_set_infinity`,
`secp_accel_normalize`, `@secpdbl`), the accelerator scratch and released heap; keeps `RG`. -/
theorem ecDouble_wn (Lo Sc Pt : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w)
    (oP : ¬ MWin Pt 96 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_ec_double) := by
  rw [edbBody_eq]; unfold edbBody
  let N0 := fun L : GA => L.lookup (ofString "pt") = some (.val (.word Pt))
  have n0u : ∀ (n : MlS), ofString "pt" ≠ n → ∀ L v, N0 L → N0 (L.update (n,v)) :=
    fun n h L v hp => by show _ = _; rw [lookup_update_ne' _ _ h]; exact hp
  have hpt : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), N0 s.locals →
      EV s (.var .local (ofString "pt")) = some (.val (.word Pt)) := fun s hp => by
    simp [EV,evalHOLExact,(show s.locals.lookup (ofString "pt") = some (.val (.word Pt)) from hp)]
  have retRG : ∀ (e : ExpHOL 64) {Q : GA → Mem → GA → Prop}, AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w
      (fun _ => False) (fun L _ G => N0 L ∧ RG Lo Sc G) Q (fun _ _ G => RG Lo Sc G) (.return e) :=
    fun e Q => aqgd_return _ (fun _ _ _ _ _ ⟨_,rg⟩ _ _ => rg)
  have decN : ∀ (n : MlS) (e : ExpHOL 64) {body : ProgHOL 64} {Q : GA → Mem → GA → Prop}, ofString "pt" ≠ n →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => N0 L ∧ RG Lo Sc G)
        (fun _ _ _ => False) (fun _ _ G => RG Lo Sc G) body →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => N0 L ∧ RG Lo Sc G)
        Q (fun _ _ G => RG Lo Sc G) (.dec n (.comb [.one,.one,.one,.one]) e body) :=
    fun n e body Q h hb => aqgd_dec (Pb := fun L _ G => N0 L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False) _ _ _
      (fun h => h.elim) (fun s v H _ hG ⟨hp,rg⟩ _ _ _ => by
        unfold GIs at hG; subst hG; exact ⟨n0u _ h _ _ hp,rg⟩) hb (fun _ _ _ _ _ _ _ h => h.elim)
  refine decN (ofString "z") _ (by decide) ?_
  refine rdecMF (LP' := N0) (ofString "zz") _ _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero) (fun L v hp => n0u _ (by decide) _ _ hp) ?_
  refine aqgd_seq (aqgd_iteT _ (retRG _) aqgd_skip) ?_
  refine decN (ofString "y") _ (by decide) ?_
  refine rdecMF (LP' := N0) (ofString "yz") _ _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero) (fun L v hp => n0u _ (by decide) _ _ hp) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_seq (rcallK (GP := RG Lo Sc) (LP := N0)
    (fun L => L.lookup (ofString "pt") = some (.val (.word Pt))) _ _ _ _ _ vmLookup_ec_set_infinity
    (ecSetInfRG Lo Sc Pt oP)
    (fun s values callee rs hp args lookup => entry_pt vmLookup_ec_set_infinity s _ Pt (hpt s hp) args lookup))
    (retRG _)) aqgd_skip) ?_
  refine rdecMF (LP' := N0) (ofString "affine") _ _ _ _ _ _ vmLookup_u256_eq
    (memoryFrame_of_good vmLookup_u256_eq (by decide) (by decide)) (by body_check Guest.guestFn_u256_eq)
    (by body_check Guest.guestFn_u256_eq) (fun L v hp => n0u _ (by decide) _ _ hp) ?_
  refine aqgd_seq (aqgd_iteT _ (rcallK (GP := RG Lo Sc) (LP := N0) (Rv := fun _ => True)
    (fun L => L.lookup (ofString "pt") = some (.val (.word Pt))) _ _ _ _ _ originalRuntimeCode_secpAccelNormalize_lookup
    (aqgd_conseq (normalize_wn Lo Sc Pt hw out oP) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs hp args lookup =>
      entry_pt originalRuntimeCode_secpAccelNormalize_lookup s _ Pt (hpt s hp) args lookup)) aqgd_skip) ?_
  refine aqgd_seq (aqgd_extCall (LP := fun L G => N0 L ∧ RG Lo Sc G) (LQ := fun L G => N0 L ∧ RG Lo Sc G) _ _ _ _ _
    (fun s _ ⟨hp,rg⟩ => ⟨Pt,64#64,hpt s hp,by simp [EV,evalHOLExact],fun j hj e => oP ⟨j,by
      have : (64#64).toNat = 64 := rfl
      omega,Or.inr e⟩,hp,rg⟩)) ?_
  refine aqgd_seq (aqgd_storeK (LP := fun L G => N0 L ∧ RG Lo Sc G) (LQ := fun L G => N0 L ∧ RG Lo Sc G) _ _
    (fun s _ ⟨hp,rg⟩ => ⟨Pt + 64#64,4,
      by simp [EV,evalHOLExact,evalListHOLExact,(show s.locals.lookup (ofString "pt") = some (.val (.word Pt)) from hp),
        wordOpHOL,wordOp,valueIsWord,valueWord],
      ev_const4_len s _ _ _ _,st4_out oP 64 (by omega),hp,rg⟩)) ?_
  exact retRG _

#print axioms ecDouble_wn

theorem ecToAffine_wn (Lo Sc Pt : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w)
    (oP : ¬ MWin Pt 96 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_ec_to_affine) := by
  rw [etaBody_eq]; unfold etaBody
  let N0 := fun L : GA => L.lookup (ofString "pt") = some (.val (.word Pt))
  have n0u : ∀ (n : MlS), ofString "pt" ≠ n → ∀ L v, N0 L → N0 (L.update (n,v)) :=
    fun n h L v hp => by show _ = _; rw [lookup_update_ne' _ _ h]; exact hp
  -- z
  refine aqgd_dec (Pb := fun L _ G => (N0 L ∧ LU4 (ofString "z") L) ∧ RG Lo Sc G) (Qb := fun _ _ _ => False)
    _ _ _ (fun h => h.elim) (fun s v H _ hG ⟨hp,rg⟩ _ ev _ => by
      unfold GIs at hG; subst hG; exact ⟨⟨n0u _ (by decide) _ _ hp,lu4_ld s _ _ v ev⟩,rg⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  refine rdecMF (LP' := fun L => N0 L ∧ LU4 (ofString "z") L) (ofString "zz") _ _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero)
    (fun L v ⟨hp,hz⟩ => ⟨n0u _ (by decide) _ _ hp,lu4_upd (by decide) _ _ hz⟩) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_return _ (fun _ _ _ _ _ ⟨_,rg⟩ _ _ => rg)) aqgd_skip) ?_
  -- zi = fp_inv(z)
  refine rdecU4 (GP := RG Lo Sc) (fun L => LU4 (ofString "a") L) _ _ _ _ _ _ _ originalRuntimeCode_fpInv_lookup
    (fpInv_wn Lo Sc hw out)
    (fun s values callee rs ⟨_,hz⟩ args lookup => entry1_u4 originalRuntimeCode_fpInv_lookup s _ hz args lookup)
    (LP' := fun L => (N0 L ∧ LU4 (ofString "z") L) ∧ LU4 (ofString "zi") L)
    (fun L v ⟨hp,hz⟩ uv => ⟨⟨n0u _ (by decide) _ _ hp,lu4_upd (by decide) _ _ hz⟩,_,lookup_update_eq' _ _ _,uv⟩) ?_
  -- zi2 = fp_sqr(zi)
  refine rdecU4 (GP := RG Lo Sc) (fun L => LU4 (ofString "a") L) _ _ _ _ _ _ _ vmLookup_fp_sqr
    (fpSqrRG Lo Sc out)
    (fun s values callee rs ⟨_,hz⟩ args lookup => entry1_u4 vmLookup_fp_sqr s _ hz args lookup)
    (LP' := fun L => ((N0 L ∧ LU4 (ofString "z") L) ∧ LU4 (ofString "zi") L) ∧ LU4 (ofString "zi2") L)
    (fun L v ⟨⟨hp,hz⟩,hzi⟩ uv => ⟨⟨⟨n0u _ (by decide) _ _ hp,lu4_upd (by decide) _ _ hz⟩,lu4_upd (by decide) _ _ hzi⟩,
      _,lookup_update_eq' _ _ _,uv⟩) ?_
  -- zi3 = fp_mul(zi2, zi)
  let N4 := fun L : GA => (((N0 L ∧ LU4 (ofString "z") L) ∧ LU4 (ofString "zi") L) ∧ LU4 (ofString "zi2") L) ∧
    LU4 (ofString "zi3") L
  refine rdecU4 (GP := RG Lo Sc) (fun L => LU4 (ofString "a") L ∧ LU4 (ofString "b") L) _ _ _ _ _ _ _ vmLookup_fp_mul
    (fpMulRG Lo Sc out)
    (fun s values callee rs ⟨⟨_,hzi⟩,hzi2⟩ args lookup =>
      entry2_u4 vmLookup_fp_mul (by decide) s _ _ hzi2 hzi args lookup) (LP' := N4)
    (fun L v ⟨⟨⟨hp,hz⟩,hzi⟩,hzi2⟩ uv => ⟨⟨⟨⟨n0u _ (by decide) _ _ hp,lu4_upd (by decide) _ _ hz⟩,
      lu4_upd (by decide) _ _ hzi⟩,lu4_upd (by decide) _ _ hzi2⟩,_,lookup_update_eq' _ _ _,uv⟩) ?_
  -- x, y
  have n4u : ∀ (n : MlS), ofString "pt" ≠ n → ofString "z" ≠ n → ofString "zi" ≠ n → ofString "zi2" ≠ n →
      ofString "zi3" ≠ n → ∀ L v, N4 L → N4 (L.update (n,v)) := fun n h1 h2 h3 h4 h5 L v ⟨⟨⟨⟨hp,hz⟩,hzi⟩,hzi2⟩,hzi3⟩ =>
    ⟨⟨⟨⟨n0u _ h1 _ _ hp,lu4_upd h2 _ _ hz⟩,lu4_upd h3 _ _ hzi⟩,lu4_upd h4 _ _ hzi2⟩,lu4_upd h5 _ _ hzi3⟩
  let N6 := fun L : GA => (N4 L ∧ LU4 (ofString "x") L) ∧ LU4 (ofString "y") L
  refine aqgd_dec (Pb := fun L _ G => (N4 L ∧ LU4 (ofString "x") L) ∧ RG Lo Sc G) (Qb := fun _ _ _ => False)
    _ _ _ (fun h => h.elim) (fun s v H _ hG ⟨n4,rg⟩ _ ev _ => by
      unfold GIs at hG; subst hG
      exact ⟨⟨n4u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ n4,lu4_ld s _ _ v ev⟩,rg⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  refine aqgd_dec (Pb := fun L _ G => N6 L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False)
    _ _ _ (fun h => h.elim) (fun s v H _ hG ⟨⟨n4,hx⟩,rg⟩ _ ev _ => by
      unfold GIs at hG; subst hG
      exact ⟨⟨⟨n4u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ n4,lu4_upd (by decide) _ _ hx⟩,
        lu4_ld s _ _ v ev⟩,rg⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  have n6x : ∀ L v, N6 L → U4V v → N6 (L.update (ofString "x",v)) := fun L v ⟨⟨n4,_⟩,hy⟩ uv =>
    ⟨⟨n4u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ n4,_,lookup_update_eq' _ _ _,uv⟩,
      lu4_upd (by decide) _ _ hy⟩
  have n6y : ∀ L v, N6 L → U4V v → N6 (L.update (ofString "y",v)) := fun L v ⟨⟨n4,hx⟩,_⟩ uv =>
    ⟨⟨n4u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ n4,lu4_upd (by decide) _ _ hx⟩,_,
      lookup_update_eq' _ _ _,uv⟩
  -- x = fp_mul(x, zi2); y = fp_mul(y, zi3)
  refine aqgd_seq (rcallU4 (GP := RG Lo Sc) (LP := N6) (fun L => LU4 (ofString "a") L ∧ LU4 (ofString "b") L) _ _ _
    _ _ _ vmLookup_fp_mul (fpMulRG Lo Sc out)
    (fun s values callee rs ⟨⟨⟨⟨_,hzi2⟩,_⟩,hx⟩,_⟩ args lookup =>
      entry2_u4 vmLookup_fp_mul (by decide) s _ _ hx hzi2 args lookup) n6x) ?_
  refine aqgd_seq (rcallU4 (GP := RG Lo Sc) (LP := N6) (fun L => LU4 (ofString "a") L ∧ LU4 (ofString "b") L) _ _ _
    _ _ _ vmLookup_fp_mul (fpMulRG Lo Sc out)
    (fun s values callee rs ⟨⟨⟨_,hzi3⟩,_⟩,hy⟩ args lookup =>
      entry2_u4 vmLookup_fp_mul (by decide) s _ _ hy hzi3 args lookup) n6y) ?_
  -- ec_set_affine(pt, x, y); return 1
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := N6)
    (fun L => L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ LU4 (ofString "x") L ∧ LU4 (ofString "y") L)
    _ _ _ _ _ vmLookup_ec_set_affine (ecSetAffineRG Lo Sc Pt oP)
    (fun s values callee rs ⟨⟨⟨⟨⟨⟨hp,_⟩,_⟩,_⟩,_⟩,hx⟩,hy⟩ args lookup =>
      entry_esa s _ Pt (by simp [EV,evalHOLExact,(show s.locals.lookup (ofString "pt") = some (.val (.word Pt)) from hp)])
        _ _ (ev_var_u4v s _ hx) (ev_var_u4v s _ hy) args lookup)) ?_
  exact aqgd_return _ (fun _ _ _ _ _ ⟨_,rg⟩ _ _ => rg)

#print axioms ecToAffine_wn
end ed
end InitECandidate.Runtime
