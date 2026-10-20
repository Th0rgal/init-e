import InitECandidate.Runtime.RecEcMulGD
import InitECandidate.Runtime.VmFn_u256_add_carry
import InitECandidate.Runtime.VmFn_u256_lt
import InitECandidate.Runtime.VmFn_fp_neg
/-!
Shape-based callee entry facts (a call proceeds only when every argument matches its parameter shape), generic rules
for pure callees with struct parameters, and the window spec of the actual `secp256k1_decompress_r(r, recid, out)`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem u4v_of_check {v : ValueHOL 64} (h : shapeEqHOL (.comb [.one,.one,.one,.one]) (shapeOfHOLExact v) = true) :
    U4V v := u4v_of_shape ((shapeEqHOL_eq_true _ _).mp h).symm

/-- Entry of a one-parameter four-word callee: the call's shape check gives the parameter a four-word value. -/
theorem entryS1 {f p : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,.comb [.one,.one,.one,.one])],bd,rs0)) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) : LU4 p callee := by
  have sh := lookupCode_shapes inst lookup
  obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
  have := evalList_nil' s _ r1; subst this
  simp only [List.zip,List.zipWith,List.all_cons,List.all_nil,Bool.and_true] at sh
  have e := callee_eq inst lookup
  exact ⟨v1,by rw [e]; simp,u4v_of_check sh⟩

theorem entryS2 {f p q : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,.comb [.one,.one,.one,.one]),(q,.comb [.one,.one,.one,.one])],
      bd,rs0)) (hpq : p ≠ q) {F : Type} (s : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64)
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1,e2] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    LU4 p callee ∧ LU4 q callee := by
  have sh := lookupCode_shapes inst lookup
  obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  simp only [List.zip,List.zipWith,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at sh
  have e := callee_eq inst lookup
  exact ⟨⟨v1,by rw [e]; simp [hpq],u4v_of_check sh.1⟩,⟨v2,by rw [e]; simp,u4v_of_check sh.2⟩⟩

theorem entry_esaS {F : Type} (s : PanSemStateFiniteExact 64 F) (e0 : ExpHOL 64) (Pt : BitVec 64)
    (h0 : EV s e0 = some (.val (.word Pt))) (e1 e2 : ExpHOL 64)
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e0,e1,e2] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ec_set_affine") values = some (body,callee,rs)) :
    callee.lookup (ofString "pt") = some (.val (.word Pt)) ∧ LU4 (ofString "x") callee ∧ LU4 (ofString "y") callee := by
  have sh := lookupCode_shapes vmLookup_ec_set_affine lookup
  obtain ⟨v0,vs,rfl,ev0,r0⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v1,vs1,rfl,_,r1⟩ := evalList_cons' s _ _ _ r0
  obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  rw [h0] at ev0; simp only [Option.some.injEq] at ev0; subst ev0
  simp only [List.zip,List.zipWith,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at sh
  have e := callee_eq vmLookup_ec_set_affine lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),⟨v1,by rw [e]; simp (config := {decide := true}),
    u4v_of_check sh.2.1⟩,⟨v2,by rw [e]; simp (config := {decide := true}),u4v_of_check sh.2.2⟩⟩

#print axioms entry_esaS

section gk
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {GP LP : GA → Prop}

/-- `x = f(args)` for a memory-and-globals-keeping callee (any parameter shapes). -/
theorem rcallMFS (x f : MlS) (args : List (ExpHOL 64)) (params : List (MlS × ShapeHOL)) (body0 : ProgHOL 64)
    (rs0 : ShapeHOL) (inst : originalRuntimeCode.lookup f = some (params,body0,rs0)) (mf : MemoryFrame body0)
    (nb : noTopBreak body0 = true) (nc : noTopContinue body0 = true) (hup : ∀ L v, LP L → LP (L.update (x,v))) :
    AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) (fun L _ G => LP L ∧ GP G) RR
      (.call (some (some (.local,x),none)) f args) :=
  aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    _ _ _ _ _ _ inst (fun _ _ _ _ _ h => h.elim) (fun h => h) (fun _ M0' G0' _ => aqgd_of_mf mf nb nc M0' G0')
    (fun s values callee rs _ H hG _ _ _ _ => by unfold GIs at hG; subst hG; exact ⟨rfl,rfl⟩)
    (fun L _ _ v _ _ ⟨lp,g⟩ ⟨_,hG⟩ => by subst hG; exact ⟨hup L v lp,g⟩)

/-- `var x = f(args); cont` for a memory-and-globals-keeping callee, `cont` finishing normally. -/
theorem rdecMFK (x f : MlS) (args : List (ExpHOL 64)) {cont : ProgHOL 64} (sh : ShapeHOL)
    (params : List (MlS × ShapeHOL)) (body0 : ProgHOL 64) (rs0 : ShapeHOL)
    (inst : originalRuntimeCode.lookup f = some (params,body0,rs0)) (mf : MemoryFrame body0)
    (nb : noTopBreak body0 = true) (nc : noTopContinue body0 = true) (hup : ∀ L v, LP L → LP (L.update (x,v)))
    (hres : ∀ L L', LP L → LP L' → LP (L'.resVarEq (x,L.lookup x)))
    (hc : AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) (fun L _ G => LP L ∧ GP G) RR cont) :
    AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) (fun L _ G => LP L ∧ GP G) RR
      (.decCall x sh f args cont) :=
  aqgd_decCall_mfF _ _ _ _ _ _ _ inst mf nb nc (fun L M G v ⟨lp,g⟩ => ⟨hup L v lp,g⟩) hc
    (fun L _ _ L' _ _ ⟨lp,_⟩ ⟨lp',g⟩ => ⟨hres L L' lp lp',g⟩)

/-- A local-keeping declaration whose body ends in a return. -/
theorem decR0 (n : MlS) (sh : ShapeHOL) (e : ExpHOL 64) {body : ProgHOL 64} {Q : GA → Mem → GA → Prop}
    (hup : ∀ L v, LP L → LP (L.update (n,v)))
    (hb : AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) (fun _ _ _ => False) RR body) :
    AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) Q RR (.dec n sh e body) :=
  aqgd_dec (Pb := fun L _ G => LP L ∧ GP G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v H _ hG ⟨lp,g⟩ _ _ _ => by unfold GIs at hG; subst hG; exact ⟨hup _ _ lp,g⟩) hb
    (fun _ _ _ _ _ _ _ h => h.elim)

#print axioms rcallMFS
end gk

def dcrBody : ProgHOL 64 :=
  (.dec (ofString "x") (.comb [.one,.one,.one,.one]) (.var .local (ofString "r")) (.seq (.ite (.cmp .equal (.op .and [(.shift .lsr (.var .local (ofString "recid")) (.const 1)),(.const 1)]) (.const 1)) (.decCall (ofString "xs") (.comb [.one,.one,.one,.one,.one]) (ofString "u256_add_carry") [(.var .local (ofString "r")),(.rstruct [(.const 13822214165235122497),(.const 13451932020343611451),(.const 18446744073709551614),(.const 18446744073709551615)])] (.seq (.ite (.cmp .equal (.rfield 4 (.var .local (ofString "xs"))) (.const 1)) (.return (.const 0)) .skip) (.assign .local (ofString "x") (.rstruct [(.rfield 0 (.var .local (ofString "xs"))),(.rfield 1 (.var .local (ofString "xs"))),(.rfield 2 (.var .local (ofString "xs"))),(.rfield 3 (.var .local (ofString "xs")))])))) .skip) (.decCall (ofString "xlt") .one (ofString "u256_lt") [(.var .local (ofString "x")),(.rstruct [(.const 18446744069414583343),(.const 18446744073709551615),(.const 18446744073709551615),(.const 18446744073709551615)])] (.seq (.ite (.cmp .equal (.var .local (ofString "xlt")) (.const 0)) (.return (.const 0)) .skip) (.decCall (ofString "rhs") (.comb [.one,.one,.one,.one]) (ofString "fp_sqr") [(.var .local (ofString "x"))] (.seq (.call (some ((some (.local,ofString "rhs")),none)) (ofString "fp_mul") [(.var .local (ofString "rhs")),(.var .local (ofString "x"))]) (.seq (.call (some ((some (.local,ofString "rhs")),none)) (ofString "fp_add") [(.var .local (ofString "rhs")),(.rstruct [(.const 7),(.const 0),(.const 0),(.const 0)])]) (.decCall (ofString "y0") (.comb [.one,.one,.one,.one]) (ofString "fp_sqrt") [(.var .local (ofString "rhs"))] (.decCall (ofString "chk") (.comb [.one,.one,.one,.one]) (ofString "fp_sqr") [(.var .local (ofString "y0"))] (.decCall (ofString "sq") .one (ofString "u256_eq") [(.var .local (ofString "chk")),(.var .local (ofString "rhs"))] (.seq (.ite (.cmp .equal (.var .local (ofString "sq")) (.const 0)) (.return (.const 0)) .skip) (.dec (ofString "y") (.comb [.one,.one,.one,.one]) (.var .local (ofString "y0")) (.seq (.ite (.cmp .notEqual (.op .and [(.rfield 0 (.var .local (ofString "y0"))),(.const 1)]) (.op .and [(.var .local (ofString "recid")),(.const 1)])) (.call (some ((some (.local,ofString "y")),none)) (ofString "fp_neg") [(.var .local (ofString "y0"))]) .skip) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.var .local (ofString "out")),(.var .local (ofString "x")),(.var .local (ofString "y"))]) (.return (.const 1))))))))))))))))

theorem dcrBody_eq : sourceFunctionBody Guest.guestFn_secp256k1_decompress_r = dcrBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_secp256k1_decompress_r,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl


section dc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- The actual `secp256k1_decompress_r(r, recid, out)`: writes only `[Out, Out + 96)` (through `ec_set_affine`), the
accelerator scratch and released heap (through `fp_sqrt`); keeps `RG`. -/
theorem decompress_wn (Lo Sc Out : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (oO : ¬ MWin Out 96 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word Out)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_secp256k1_decompress_r) := by
  rw [dcrBody_eq]; unfold dcrBody
  let DO := fun L : GA => L.lookup (ofString "out") = some (.val (.word Out))
  have hu : ∀ (n : MlS), ofString "out" ≠ n → ∀ L v, DO L → DO (L.update (n,v)) :=
    fun n h L v hp => by show _ = _; rw [lookup_update_ne' _ _ h]; exact hp
  have hr : ∀ (n : MlS), ofString "out" ≠ n → ∀ (L L' : GA), DO L → DO L' → DO (L'.resVarEq (n,L.lookup n)) :=
    fun n h L L' _ hp => by show _ = _; rw [resVarEq_lookup_ne' _ _ _ _ h]; exact hp
  refine decR0 (LP := DO) (GP := RG Lo Sc) _ _ _ (hu _ (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ ?_ aqgd_skip) ?_
  · refine rdecMFK (LP := DO) (GP := RG Lo Sc) (ofString "xs") _ _ _ _ _ _ vmLookup_u256_add_carry
      (memoryFrame_of_good vmLookup_u256_add_carry (by decide) (by decide))
      (by body_check Guest.guestFn_u256_add_carry) (by body_check Guest.guestFn_u256_add_carry)
      (hu _ (by decide)) (hr _ (by decide)) ?_
    exact aqgd_seq (aqgd_iteT _ (retRG Lo Sc _) aqgd_skip)
      (aqgd_assignLocal _ _ (fun s v _ _ ⟨lp,g⟩ _ _ => ⟨hu _ (by decide) _ _ lp,g⟩))
  refine rdecMF (LP' := DO) (ofString "xlt") _ _ _ _ _ _ vmLookup_u256_lt
    (memoryFrame_of_good vmLookup_u256_lt (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt)
    (by body_check Guest.guestFn_u256_lt) (hu _ (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (retRG Lo Sc _) aqgd_skip) ?_
  refine rdecU4 (GP := RG Lo Sc) (LP' := DO) (fun L => LU4 (ofString "a") L) (ofString "rhs") _ _ _ _ _ _
    vmLookup_fp_sqr (fpSqrRG Lo Sc out)
    (fun s values callee rs _ args lookup => entryS1 vmLookup_fp_sqr s _ args lookup)
    (fun L v lp _ => hu _ (by decide) _ _ lp) ?_
  refine aqgd_seq (rcallU4 (GP := RG Lo Sc) (LP := DO) (fun L => LU4 (ofString "a") L ∧ LU4 (ofString "b") L)
    (ofString "rhs") _ _ _ _ _ vmLookup_fp_mul (fpMulRG Lo Sc out)
    (fun s values callee rs _ args lookup => entryS2 vmLookup_fp_mul (by decide) s _ _ args lookup)
    (fun L v lp _ => hu _ (by decide) _ _ lp)) ?_
  refine aqgd_seq (rcallMFS (LP := DO) (GP := RG Lo Sc) (ofString "rhs") _ _ _ _ _ vmLookup_fp_add
    (memoryFrame_of_good vmLookup_fp_add (by decide) (by decide)) (by body_check Guest.guestFn_fp_add)
    (by body_check Guest.guestFn_fp_add) (hu _ (by decide))) ?_
  refine rdecU4 (GP := RG Lo Sc) (LP' := DO) (fun L => LU4 (ofString "a") L) (ofString "y0") _ _ _ _ _ _
    originalRuntimeCode_fpSqrt_lookup (fpSqrt_wn Lo Sc hw out)
    (fun s values callee rs _ args lookup => entryS1 originalRuntimeCode_fpSqrt_lookup s _ args lookup)
    (fun L v lp _ => hu _ (by decide) _ _ lp) ?_
  refine rdecU4 (GP := RG Lo Sc) (LP' := DO) (fun L => LU4 (ofString "a") L) (ofString "chk") _ _ _ _ _ _
    vmLookup_fp_sqr (fpSqrRG Lo Sc out)
    (fun s values callee rs _ args lookup => entryS1 vmLookup_fp_sqr s _ args lookup)
    (fun L v lp _ => hu _ (by decide) _ _ lp) ?_
  refine rdecMF (LP' := DO) (ofString "sq") _ _ _ _ _ _ vmLookup_u256_eq
    (memoryFrame_of_good vmLookup_u256_eq (by decide) (by decide)) (by body_check Guest.guestFn_u256_eq)
    (by body_check Guest.guestFn_u256_eq) (hu _ (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (retRG Lo Sc _) aqgd_skip) ?_
  refine decR0 (LP := DO) (GP := RG Lo Sc) _ _ _ (hu _ (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (rcallMFS (LP := DO) (GP := RG Lo Sc) (ofString "y") _ _ _ _ _ vmLookup_fp_neg
    (memoryFrame_of_good vmLookup_fp_neg (by decide) (by decide)) (by body_check Guest.guestFn_fp_neg)
    (by body_check Guest.guestFn_fp_neg) (hu _ (by decide))) aqgd_skip) ?_
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := DO)
    (fun L => L.lookup (ofString "pt") = some (.val (.word Out)) ∧ LU4 (ofString "x") L ∧ LU4 (ofString "y") L)
    _ _ _ _ _ vmLookup_ec_set_affine (ecSetAffineRG Lo Sc Out oO)
    (fun s values callee rs hp args lookup => entry_esaS s _ Out
      (by simp [EV,evalHOLExact,(show s.locals.lookup (ofString "out") = some (.val (.word Out)) from hp)]) _ _
      args lookup)) ?_
  exact retRG Lo Sc _

#print axioms decompress_wn
end dc
end InitECandidate.Runtime
