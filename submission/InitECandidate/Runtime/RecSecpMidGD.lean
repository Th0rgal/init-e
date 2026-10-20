import InitECandidate.Runtime.RecPowGD
import InitECandidate.Runtime.OriginalRecoverCode
import InitECandidate.Runtime.VmFn_ec_set_affine
/-!
Generic call rules for four-word callees keeping a globals predicate (`rcallU4`, `rdecU4`, `rcallK`), callee entry
facts, `RG`-lifted multiplier specs, and the window specs of the actual `fp_inv` / `fn_inv` / `fp_sqrt` (tail calls
of the exponentiations) and `secp_accel_normalize(pt)` (writes only `[Pt, Pt + 96)`, the scratch and released heap).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful callee lookup checked every argument against its parameter shape. -/
theorem lookupCode_shapes {f : MlS} {params : List (MlS × ShapeHOL)} {body' : ProgHOL 64} {rs' : ShapeHOL}
    (hcode : originalRuntimeCode.lookup f = some (params,body',rs')) {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (h : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    (params.zip values).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i b cl r hl
    unfold lookupCodeHOLExact at hl
    rw [hcode] at hl
    simp only at hl
    split_ifs at hl with hc
    exact hc.2.2

#print axioms lookupCode_shapes

def fpInvBody : ProgHOL 64 :=
  (.call none (ofString "secp_accel_fp_pow4") [(.var .local (ofString "a")),(.rstruct [(.const 18446744069414583341),(.const 18446744073709551615),(.const 18446744073709551615),(.const 18446744073709551615)])])

theorem fpInvBody_eq : sourceFunctionBody Guest.guestFn_fp_inv = fpInvBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_fp_inv,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def fnInvBody : ProgHOL 64 :=
  (.call none (ofString "secp_accel_fn_pow4") [(.var .local (ofString "a")),(.rstruct [(.const 13822214165235122495),(.const 13451932020343611451),(.const 18446744073709551614),(.const 18446744073709551615)])])

theorem fnInvBody_eq : sourceFunctionBody Guest.guestFn_fn_inv = fnInvBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_fn_inv,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def fpSqrtBody : ProgHOL 64 :=
  (.call none (ofString "secp_accel_fp_pow4") [(.var .local (ofString "a")),(.rstruct [(.const 18446744072635809548),(.const 18446744073709551615),(.const 18446744073709551615),(.const 4611686018427387903)])])

theorem fpSqrtBody_eq : sourceFunctionBody Guest.guestFn_fp_sqrt = fpSqrtBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_fp_sqrt,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl


section inv
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- Tail call `pow(a, E)` of an exponentiation with spec `hpow`. -/
theorem powTail_wn (Lo Sc : BitVec 64) (callee0 : MlS) (body0 : ProgHOL 64)
    (inst : originalRuntimeCode.lookup callee0 = some ([(ofString "a",.comb [.one,.one,.one,.one]),
      (ofString "e",.comb [.one,.one,.one,.one])],body0,.comb [.one,.one,.one,.one]))
    (hpow : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G) (fun _ _ _ => True) (fun r _ G => U4V r ∧ RG Lo Sc G) body0)
    (e2 : ExpHOL 64) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ RG Lo Sc G) (.call none callee0 [.var .local (ofString "a"),e2]) :=
  aqgd_tailCallSpecS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G)
    (RRe := fun _ _ _ r _ G => U4V r ∧ RG Lo Sc G) _ _ _ _ _ inst (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ => hpow)
    (fun s values callee rs _ H hG ⟨⟨va,ha,ua⟩,hrg⟩ _ args lookup => by
      unfold GIs at hG; subst hG
      obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
      have := evalList_nil' s _ r2; subst this
      simp [EV,evalHOLExact,ha] at ev1; subst ev1
      have e := callee_eq inst lookup
      exact ⟨⟨va,by rw [e]; simp (config := {decide := true}),ua⟩,hrg⟩)
    (fun _ _ _ _ _ _ _ h => h)

theorem fpInv_wn (Lo Sc : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_fp_inv) := by
  rw [fpInvBody_eq]; unfold fpInvBody
  exact powTail_wn Lo Sc _ _ originalRuntimeCode_secpAccelFpPow4_lookup (fpPow4_wn Lo Sc hw out) _

theorem fnInv_wn (Lo Sc : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_fn_inv) := by
  rw [fnInvBody_eq]; unfold fnInvBody
  exact powTail_wn Lo Sc _ _ originalRuntimeCode_secpAccelFnPow4_lookup (fnPow4_wn Lo Sc hw out) _

theorem fpSqrt_wn (Lo Sc : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_fp_sqrt) := by
  rw [fpSqrtBody_eq]; unfold fpSqrtBody
  exact powTail_wn Lo Sc _ _ originalRuntimeCode_secpAccelFpPow4_lookup (fpPow4_wn Lo Sc hw out) _

#print axioms fpSqrt_wn
end inv
section gen
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A globals-keeping callee keeps any globals predicate. -/
theorem spec_keep {GP GI : GA → Prop} {Pe : GA → Prop} {Rv : ValueHOL 64 → Prop} {body : ProgHOL 64}
    (hk : keepsGA goodGA body = true)
    (h : AQGD D B A w (fun _ => False) (fun L _ G => Pe L ∧ GP G) (fun _ _ _ => True) (fun r _ G => Rv r ∧ GP G) body) :
    AQGD D B A w (fun _ => False) (fun L _ G => Pe L ∧ GP G ∧ GI G) (fun _ _ _ => True)
      (fun r _ G => Rv r ∧ GP G ∧ GI G) body :=
  aqgd_conseq (aqgd_keepGI (GI := GI) hk h) (fun _ _ _ ⟨p,g,i⟩ => ⟨⟨p,g⟩,i⟩) (fun _ _ _ _ => trivial)
    (fun _ _ _ ⟨⟨r,g⟩,i⟩ => ⟨r,g,i⟩)

/-- `x = f(args)` (or `var x = f(args)` continuation-free form) for a callee returning a four-word value and keeping
the globals predicate `GP`. -/
theorem rcallU4 {GP : GA → Prop} {LP : GA → Prop} (Pe : GA → Prop) (x f : MlS) (args : List (ExpHOL 64))
    (params : List (MlS × ShapeHOL)) (body0 : ProgHOL 64) (rs0 : ShapeHOL)
    (inst : originalRuntimeCode.lookup f = some (params,body0,rs0))
    (hb : AQGD D B A w (fun _ => False) (fun L _ G => Pe L ∧ GP G) (fun _ _ _ => True)
      (fun r _ G => U4V r ∧ GP G) body0)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body0,callee,rs) → Pe callee)
    (hup : ∀ L v, LP L → U4V v → LP (L.update (x,v))) :
    AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) (fun L _ G => LP L ∧ GP G) RR
      (.call (some (some (.local,x),none)) f args) :=
  aqgd_callAssignFS (Vn' := fun _ => False) (Pe := fun _ _ _ L _ G => Pe L ∧ GP G)
    (RRe := fun _ _ _ r _ G => U4V r ∧ GP G) _ _ _ _ _ _ inst (fun _ _ _ _ _ h => h.elim) (fun h => h)
    (fun _ _ _ _ => hb)
    (fun s values callee rs _ H hG ⟨lp,g⟩ _ args lookup => by
      unfold GIs at hG; subst hG; exact ⟨hpe s values callee rs lp args lookup,g⟩)
    (fun L _ _ v _ _ ⟨lp,_⟩ ⟨uv,g⟩ => ⟨hup L v lp uv,g⟩)

/-- `var x = f(args); cont` for a callee returning a four-word value and keeping `GP`; `cont` ends in a return. -/
theorem rdecU4 {GP : GA → Prop} {LP LP' : GA → Prop} {Q : GA → Mem → GA → Prop} (Pe : GA → Prop) (x f : MlS)
    (args : List (ExpHOL 64)) {cont : ProgHOL 64} (sh : ShapeHOL)
    (params : List (MlS × ShapeHOL)) (body0 : ProgHOL 64) (rs0 : ShapeHOL)
    (inst : originalRuntimeCode.lookup f = some (params,body0,rs0))
    (hb : AQGD D B A w (fun _ => False) (fun L _ G => Pe L ∧ GP G) (fun _ _ _ => True)
      (fun r _ G => U4V r ∧ GP G) body0)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body0,callee,rs) → Pe callee)
    (hup : ∀ L v, LP L → U4V v → LP' (L.update (x,v)))
    (hc : AQGD D B A w (fun _ => False) (fun L _ G => LP' L ∧ GP G) (fun _ _ _ => False) RR cont) :
    AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) Q RR (.decCall x sh f args cont) :=
  aqgd_decCallSpecS (Vn' := fun _ => False) (Pe := fun _ _ _ L _ G => Pe L ∧ GP G)
    (RRe := fun _ _ _ r _ G => U4V r ∧ GP G) _ _ _ _ _ _ _ inst (fun _ _ _ _ _ h => h.elim) (fun _ _ _ _ => hb)
    (fun s values callee rs _ H hG ⟨lp,g⟩ _ args lookup => by
      unfold GIs at hG; subst hG; exact ⟨hpe s values callee rs lp args lookup,g⟩) (fun h => h.elim)
    (fun L _ _ v _ _ ⟨lp,_⟩ ⟨uv,g⟩ _ => ⟨hup L v lp uv,g⟩) hc (fun _ _ _ _ _ _ _ h => h.elim)

/-- `f(args)` (result discarded) for a callee keeping `GP`. -/
theorem rcallK {GP : GA → Prop} {LP : GA → Prop} (Pe : GA → Prop) (f : MlS) (args : List (ExpHOL 64))
    (params : List (MlS × ShapeHOL)) (body0 : ProgHOL 64) (rs0 : ShapeHOL)
    (inst : originalRuntimeCode.lookup f = some (params,body0,rs0)) {Rv : ValueHOL 64 → Prop}
    (hb : AQGD D B A w (fun _ => False) (fun L _ G => Pe L ∧ GP G) (fun _ _ _ => True)
      (fun r _ G => Rv r ∧ GP G) body0)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body0,callee,rs) → Pe callee) :
    AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) (fun L _ G => LP L ∧ GP G) RR
      (.call (some (none,none)) f args) :=
  aqgd_callSpecS (Vn' := fun _ => False) (Pe := fun _ _ _ L _ G => Pe L ∧ GP G)
    (RRe := fun _ _ _ r _ G => Rv r ∧ GP G) _ _ _ _ _ inst (fun _ _ _ _ _ h => h.elim) (fun _ _ _ _ => hb)
    (fun s values callee rs _ H hG ⟨lp,g⟩ _ args lookup => by
      unfold GIs at hG; subst hG; exact ⟨hpe s values callee rs lp args lookup,g⟩)
    (fun L _ _ v _ _ ⟨lp,_⟩ ⟨_,g⟩ => ⟨lp,g⟩)

#print axioms rcallK
end gen

theorem entry1_u4 {f p : MlS} {sh : ShapeHOL} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,sh)],bd,rs0)) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (hx : LU4 x s.locals) {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.var .local x] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) : LU4 p callee := by
  obtain ⟨u,hu,uu⟩ := hx
  obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
  have := evalList_nil' s _ r1; subst this
  simp [EV,evalHOLExact,hu] at ev1; subst ev1
  have e := callee_eq inst lookup
  exact ⟨u,by rw [e]; simp,uu⟩

theorem entry2_u4 {f p q : MlS} {sh sh' : ShapeHOL} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,sh),(q,sh')],bd,rs0)) (hpq : p ≠ q) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x y : MlS) (hx : LU4 x s.locals) (hy : LU4 y s.locals)
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local x,.var .local y] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    LU4 p callee ∧ LU4 q callee := by
  obtain ⟨u,hu,uu⟩ := hx
  obtain ⟨u',hu',uu'⟩ := hy
  obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  simp [EV,evalHOLExact,hu] at ev1; subst ev1
  simp [EV,evalHOLExact,hu'] at ev2; subst ev2
  have e := callee_eq inst lookup
  exact ⟨⟨u,by rw [e]; simp [hpq],uu⟩,⟨u',by rw [e]; simp,uu'⟩⟩

/-- Entry of `ec_set_affine(e0, x, y)` with `e0` evaluating to `Pt`. -/
theorem entry_esa {F : Type} (s : PanSemStateFiniteExact 64 F) (e0 : ExpHOL 64) (Pt : BitVec 64)
    (h0 : EV s e0 = some (.val (.word Pt))) (e1 e2 : ExpHOL 64)
    (h1 : ∀ v, EV s e1 = some v → U4V v) (h2 : ∀ v, EV s e2 = some v → U4V v)
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e0,e1,e2] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ec_set_affine") values = some (body,callee,rs)) :
    callee.lookup (ofString "pt") = some (.val (.word Pt)) ∧ LU4 (ofString "x") callee ∧ LU4 (ofString "y") callee := by
  obtain ⟨v0,vs,rfl,ev0,r0⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v1,vs1,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ r0
  obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  rw [h0] at ev0; simp only [Option.some.injEq] at ev0; subst ev0
  have e := callee_eq vmLookup_ec_set_affine lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),⟨v1,by rw [e]; simp (config := {decide := true}),h1 _ ev1⟩,
    ⟨v2,by rw [e]; simp (config := {decide := true}),h2 _ ev2⟩⟩

theorem ev_var_u4v {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (h : LU4 x s.locals) :
    ∀ v, EV s (.var .local x) = some v → U4V v := fun v ev => by
  obtain ⟨u,hu,uu⟩ := h; simp [EV,evalHOLExact,hu] at ev; subst ev; exact uu

def nrmBody : ProgHOL 64 :=
  (.dec (ofString "z") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pt")),(.const 64)])) (.decCall (ofString "zi") (.comb [.one,.one,.one,.one]) (ofString "fp_inv") [(.var .local (ofString "z"))] (.decCall (ofString "zi2") (.comb [.one,.one,.one,.one]) (ofString "fp_sqr") [(.var .local (ofString "zi"))] (.decCall (ofString "zi3") (.comb [.one,.one,.one,.one]) (ofString "fp_mul") [(.var .local (ofString "zi2")),(.var .local (ofString "zi"))] (.dec (ofString "x") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.var .local (ofString "pt"))) (.dec (ofString "y") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pt")),(.const 32)])) (.seq (.call (some ((some (.local,ofString "x")),none)) (ofString "fp_mul") [(.var .local (ofString "x")),(.var .local (ofString "zi2"))]) (.seq (.call (some ((some (.local,ofString "y")),none)) (ofString "fp_mul") [(.var .local (ofString "y")),(.var .local (ofString "zi3"))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.var .local (ofString "pt")),(.var .local (ofString "x")),(.var .local (ofString "y"))]) (.return (.const 1)))))))))))

theorem nrmBody_eq : sourceFunctionBody Guest.guestFn_secp_accel_normalize = nrmBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_secp_accel_normalize,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl


section nm
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

theorem toRG {Lo Sc : BitVec 64} {Pe : GA → Prop} {Rv : ValueHOL 64 → Prop} {body : ProgHOL 64}
    {A : GA → Prop}
    (h : AQGD D B A w (fun _ => False) (fun L _ G => Pe L ∧ ScrIs Sc G ∧ HGe Lo G) (fun _ _ _ => True)
      (fun r _ G => Rv r ∧ ScrIs Sc G ∧ HGe Lo G) body) :
    AQGD D B A w (fun _ => False) (fun L _ G => Pe L ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun r _ G => Rv r ∧ RG Lo Sc G) body :=
  aqgd_conseq h (fun _ _ _ ⟨p,h,s⟩ => ⟨p,s,h⟩) (fun _ _ _ h => h) (fun _ _ _ ⟨r,s,h⟩ => ⟨r,h,s⟩)

theorem fpMulRG (Lo Sc : BitVec 64) (out : ¬ MWin Sc 448 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun r _ G => U4V r ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_fp_mul) :=
  toRG (spec_keep (keepsGA_of_installed vmLookup_fp_mul (by decide)) (fpMul_wn Sc out))

theorem fpSqrRG (Lo Sc : BitVec 64) (out : ¬ MWin Sc 448 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_fp_sqr) :=
  toRG (spec_keep (keepsGA_of_installed vmLookup_fp_sqr (by decide)) (fpSqr_wn Sc out))

theorem fnMulRG (Lo Sc : BitVec 64) (out : ¬ MWin Sc 448 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun r _ G => U4V r ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_fn_mul) :=
  toRG (spec_keep (keepsGA_of_installed vmLookup_fn_mul (by decide)) (fnMul_wn Sc out))

theorem ecSetAffineRG (Lo Sc Pt : BitVec 64) (out : ¬ MWin Pt 96 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ LU4 (ofString "x") L ∧ LU4 (ofString "y") L) ∧
        RG Lo Sc G) (fun _ _ _ => True) (fun _ _ G => True ∧ RG Lo Sc G)
      (sourceFunctionBody Guest.guestFn_ec_set_affine) :=
  aqgd_conseq (aqgd_keepGI (GI := RG Lo Sc) (keepsGA_of_installed vmLookup_ec_set_affine (by decide))
    (ecSetAffine_wn Pt out)) (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

#print axioms ecSetAffineRG

theorem lu4_ld {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (e : ExpHOL 64) (v : ValueHOL 64)
    (ev : EV s (.load (.comb [.one,.one,.one,.one]) e) = some v) : LU4 x (s.locals.update (x,v)) :=
  ⟨v,lookup_update_eq' _ _ _,ev_load_u4 s _ v ev⟩

/-- The actual `secp_accel_normalize(pt)`: writes only `[Pt, Pt + 96)`, the accelerator scratch, and temporary heap
blocks at or above the heap pointer (released); keeps `RG`. -/
theorem normalize_wn (Lo Sc Pt : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w)
    (oP : ¬ MWin Pt 96 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "pt") = some (.val (.word Pt)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_secp_accel_normalize) := by
  rw [nrmBody_eq]; unfold nrmBody
  let N0 := fun L : GA => L.lookup (ofString "pt") = some (.val (.word Pt))
  have n0u : ∀ (n : MlS), ofString "pt" ≠ n → ∀ L v, N0 L → N0 (L.update (n,v)) :=
    fun n h L v hp => by show _ = _; rw [lookup_update_ne' _ _ h]; exact hp
  -- z
  refine aqgd_dec (Pb := fun L _ G => (N0 L ∧ LU4 (ofString "z") L) ∧ RG Lo Sc G) (Qb := fun _ _ _ => False)
    _ _ _ (fun h => h.elim) (fun s v H _ hG ⟨hp,rg⟩ _ ev _ => by
      unfold GIs at hG; subst hG; exact ⟨⟨n0u _ (by decide) _ _ hp,lu4_ld s _ _ v ev⟩,rg⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
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

#print axioms normalize_wn
end nm
end InitECandidate.Runtime
