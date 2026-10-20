import InitECandidate.Runtime.RecDecompGD
import InitECandidate.Runtime.OriginalU256FromBeCode
import InitECandidate.Runtime.VmFn_u256_sub
/-!
Window spec of the actual `secp256k1_recover(msg_hash, r, s, recid, out)` (split `srTop` / `srMid` / `srPost`): the
two 96-byte points are fresh heap blocks above the fence, the public key is written only to `[Out, Out + 64)`, the heap
is released to the mark; `RG` is kept.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def srPost : ProgHOL 64 :=
  (.dec (ofString "rx") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.var .local (ofString "pr"))) (.dec (ofString "ry") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pr")),(.const 32)])) (.decCall (ofString "e") (.comb [.one,.one,.one,.one]) (ofString "u256_from_be") [(.var .local (ofString "msg_hash")),(.const 32)] (.decCall (ofString "elt") .one (ofString "u256_lt") [(.var .local (ofString "e")),(.rstruct [(.const 13822214165235122497),(.const 13451932020343611451),(.const 18446744073709551614),(.const 18446744073709551615)])] (.seq (.ite (.cmp .equal (.var .local (ofString "elt")) (.const 0)) (.call (some ((some (.local,ofString "e")),none)) (ofString "u256_sub") [(.var .local (ofString "e")),(.rstruct [(.const 13822214165235122497),(.const 13451932020343611451),(.const 18446744073709551614),(.const 18446744073709551615)])]) .skip) (.decCall (ofString "rinv") (.comb [.one,.one,.one,.one]) (ofString "fn_inv") [(.var .local (ofString "r"))] (.dec (ofString "nege") (.comb [.one,.one,.one,.one]) (.rstruct [(.const 0),(.const 0),(.const 0),(.const 0)]) (.decCall (ofString "ez") .one (ofString "u256_is_zero") [(.var .local (ofString "e"))] (.seq (.ite (.cmp .equal (.var .local (ofString "ez")) (.const 0)) (.call (some ((some (.local,ofString "nege")),none)) (ofString "u256_sub") [(.rstruct [(.const 13822214165235122497),(.const 13451932020343611451),(.const 18446744073709551614),(.const 18446744073709551615)]),(.var .local (ofString "e"))]) .skip) (.decCall (ofString "u1") (.comb [.one,.one,.one,.one]) (ofString "fn_mul") [(.var .local (ofString "nege")),(.var .local (ofString "rinv"))] (.decCall (ofString "u2") (.comb [.one,.one,.one,.one]) (ofString "fn_mul") [(.var .local (ofString "s")),(.var .local (ofString "rinv"))] (.seq (.call (some (none,none)) (ofString "ec_mul2") [(.var .local (ofString "pq")),(.var .local (ofString "u1")),(.rstruct [(.const 6481385041966929816),(.const 188021827762530521),(.const 6170039885052185351),(.const 8772561819708210092)]),(.rstruct [(.const 11261198710074299576),(.const 18237243440184513561),(.const 6747795201694173352),(.const 5204712524664259685)]),(.var .local (ofString "u2")),(.var .local (ofString "rx")),(.var .local (ofString "ry"))]) (.decCall (ofString "ok") .one (ofString "ec_to_affine") [(.var .local (ofString "pq"))] (.seq (.ite (.cmp .equal (.var .local (ofString "ok")) (.const 1)) (.dec (ofString "qx") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.var .local (ofString "pq"))) (.dec (ofString "qy") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "pq")),(.const 32)])) (.seq (.call (some (none,none)) (ofString "u256_to_be32") [(.var .local (ofString "qx")),(.var .local (ofString "out"))]) (.call (some (none,none)) (ofString "u256_to_be32") [(.var .local (ofString "qy")),(.op .add [(.var .local (ofString "out")),(.const 32)])])))) .skip) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.var .local (ofString "ok"))))))))))))))))))

def srMid : ProgHOL 64 :=
  (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "pq") .one (ofString "alloc") [(.const 96)] (.decCall (ofString "pr") .one (ofString "alloc") [(.const 96)] (.decCall (ofString "okr") .one (ofString "secp256k1_decompress_r") [(.var .local (ofString "r")),(.var .local (ofString "recid")),(.var .local (ofString "pr"))] (.seq (.ite (.cmp .equal (.var .local (ofString "okr")) (.const 0)) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.const 0))) .skip) srPost)))))

def srTop : ProgHOL 64 :=
  (.decCall (ofString "rz") .one (ofString "u256_is_zero") [(.var .local (ofString "r"))] (.seq (.ite (.cmp .equal (.var .local (ofString "rz")) (.const 1)) (.return (.const 0)) .skip) (.decCall (ofString "rlt") .one (ofString "u256_lt") [(.var .local (ofString "r")),(.rstruct [(.const 13822214165235122497),(.const 13451932020343611451),(.const 18446744073709551614),(.const 18446744073709551615)])] (.seq (.ite (.cmp .equal (.var .local (ofString "rlt")) (.const 0)) (.return (.const 0)) .skip) (.decCall (ofString "sz") .one (ofString "u256_is_zero") [(.var .local (ofString "s"))] (.seq (.ite (.cmp .equal (.var .local (ofString "sz")) (.const 1)) (.return (.const 0)) .skip) (.decCall (ofString "slt") .one (ofString "u256_lt") [(.var .local (ofString "s")),(.rstruct [(.const 13822214165235122497),(.const 13451932020343611451),(.const 18446744073709551614),(.const 18446744073709551615)])] (.seq (.ite (.cmp .equal (.var .local (ofString "slt")) (.const 0)) (.return (.const 0)) .skip) srMid))))))))

theorem srTop_eq : sourceFunctionBody Guest.guestFn_secp256k1_recover = srTop := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_secp256k1_recover,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

section gk2
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {GP LP : GA → Prop}

/-- A local-keeping declaration whose body finishes normally. -/
theorem decRK (n : MlS) (sh : ShapeHOL) (e : ExpHOL 64) {body : ProgHOL 64}
    (hup : ∀ L v, LP L → LP (L.update (n,v))) (hres : ∀ L L', LP L → LP L' → LP (L'.resVarEq (n,L.lookup n)))
    (hb : AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) (fun L _ G => LP L ∧ GP G) RR body) :
    AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) (fun L _ G => LP L ∧ GP G) RR (.dec n sh e body) :=
  aqgd_dec (Pb := fun L _ G => LP L ∧ GP G) (Qb := fun L _ G => LP L ∧ GP G) _ _ _ (fun h => h.elim)
    (fun s v H _ hG ⟨lp,g⟩ _ _ _ => by unfold GIs at hG; subst hG; exact ⟨hup _ _ lp,g⟩) hb
    (fun L _ _ L' _ _ ⟨lp,_⟩ ⟨lp',g⟩ => ⟨hres L L' lp lp',g⟩)

/-- `var x = f(args); cont` for a callee keeping `GP` (any result), `cont` ending in a return. -/
theorem rdecAny {LP' : GA → Prop} {Q : GA → Mem → GA → Prop} (Pe : GA → Prop) (x f : MlS)
    (args : List (ExpHOL 64)) {cont : ProgHOL 64} (sh : ShapeHOL)
    (params : List (MlS × ShapeHOL)) (body0 : ProgHOL 64) (rs0 : ShapeHOL)
    (inst : originalRuntimeCode.lookup f = some (params,body0,rs0))
    (hb : AQGD D B A w (fun _ => False) (fun L _ G => Pe L ∧ GP G) (fun _ _ _ => True) (fun _ _ G => GP G) body0)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body0,callee,rs) → Pe callee)
    (hup : ∀ L v, LP L → LP' (L.update (x,v)))
    (hc : AQGD D B A w (fun _ => False) (fun L _ G => LP' L ∧ GP G) (fun _ _ _ => False) RR cont) :
    AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ GP G) Q RR (.decCall x sh f args cont) :=
  aqgd_decCallSpecS (Vn' := fun _ => False) (Pe := fun _ _ _ L _ G => Pe L ∧ GP G)
    (RRe := fun _ _ _ _ _ G => GP G) _ _ _ _ _ _ _ inst (fun _ _ _ _ _ h => h.elim) (fun _ _ _ _ => hb)
    (fun s values callee rs _ H hG ⟨lp,g⟩ _ args lookup => by
      unfold GIs at hG; subst hG; exact ⟨hpe s values callee rs lp args lookup,g⟩) (fun h => h.elim)
    (fun L _ _ v _ _ ⟨lp,_⟩ g _ => ⟨hup L v lp,g⟩) hc (fun _ _ _ _ _ _ _ h => h.elim)

#print axioms rdecAny
end gk2

/-- Entry of `ec_mul2(e0, ...)`: `out` from `e0`, the base coordinates four-word by the shape check. -/
theorem entry_em2S {F : Type} (s : PanSemStateFiniteExact 64 F) (e0 e1 e2 e3 e4 e5 e6 : ExpHOL 64) (Out : BitVec 64)
    (h0 : EV s e0 = some (.val (.word Out))) {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA}
    {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e0,e1,e2,e3,e4,e5,e6] =
      some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ec_mul2") values = some (body,callee,rs)) :
    EM0 Out callee := by
  have sh := lookupCode_shapes originalRuntimeCode_ecMul2_lookup lookup
  obtain ⟨v0,vs,rfl,ev0,r0⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v1,vs1,rfl,_,r1⟩ := evalList_cons' s _ _ _ r0
  obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
  obtain ⟨v3,vs3,rfl,_,r3⟩ := evalList_cons' s _ _ _ r2
  obtain ⟨v4,vs4,rfl,_,r4⟩ := evalList_cons' s _ _ _ r3
  obtain ⟨v5,vs5,rfl,_,r5⟩ := evalList_cons' s _ _ _ r4
  obtain ⟨v6,vs6,rfl,_,r6⟩ := evalList_cons' s _ _ _ r5
  have := evalList_nil' s _ r6; subst this
  rw [h0] at ev0; simp only [Option.some.injEq] at ev0; subst ev0
  simp only [List.zip,List.zipWith,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at sh
  have e := callee_eq originalRuntimeCode_ecMul2_lookup lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),⟨v2,by rw [e]; simp (config := {decide := true}),
    u4v_of_check sh.2.2.1⟩,⟨v3,by rw [e]; simp (config := {decide := true}),u4v_of_check sh.2.2.2.1⟩,
    ⟨v5,by rw [e]; simp (config := {decide := true}),u4v_of_check sh.2.2.2.2.2.1⟩,
    ⟨v6,by rw [e]; simp (config := {decide := true}),u4v_of_check sh.2.2.2.2.2.2⟩⟩

/-- Entry of `u256_to_be32(e1, e2)`: `out` from `e2`. -/
theorem entry_u2b {F : Type} (s : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64) (O : BitVec 64)
    (h2 : EV s e2 = some (.val (.word O))) {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA}
    {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1,e2] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_to_be32") values = some (body,callee,rs)) :
    callee.lookup (ofString "out") = some (.val (.word O)) := by
  obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  rw [h2] at ev2; simp only [Option.some.injEq] at ev2; subst ev2
  have e := callee_eq vmLookup_u256_to_be32 lookup
  rw [e]; simp (config := {decide := true})

section u2
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

theorem u2bRG (Lo Sc O : BitVec 64) (out : ¬ MWin O 32 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word O)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => True ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_u256_to_be32) :=
  aqgd_conseq (aqgd_keepGI (GI := RG Lo Sc) (keepsGA_of_installed vmLookup_u256_to_be32 (by decide))
    (u2b_wn O out)) (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

#print axioms u2bRG

/-- Locals of `secp256k1_recover` after the allocations. -/
def SRL (Out H : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "out") = some (.val (.word Out)) ∧ L.lookup (ofString "mark") = some (.val (.word H)) ∧
    L.lookup (ofString "pq") = some (.val (.word H))

theorem srl_upd {Out H : BitVec 64} (n : MlS) (h1 : ofString "out" ≠ n) (h2 : ofString "mark" ≠ n)
    (h3 : ofString "pq" ≠ n) (L : GA) (v : ValueHOL 64) (h : SRL Out H L) : SRL Out H (L.update (n,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.2.2⟩

theorem srl_res {Out H : BitVec 64} (n : MlS) (h1 : ofString "out" ≠ n) (h2 : ofString "mark" ≠ n)
    (h3 : ofString "pq" ≠ n) (L L' : GA) (_ : SRL Out H L) (h : SRL Out H L') : SRL Out H (L'.resVarEq (n,L.lookup n)) :=
  ⟨by rw [resVarEq_lookup_ne' _ _ _ _ h1]; exact h.1,by rw [resVarEq_lookup_ne' _ _ _ _ h2]; exact h.2.1,
    by rw [resVarEq_lookup_ne' _ _ _ _ h3]; exact h.2.2⟩

/-- `secp256k1_recover` after the decompression: scalar arithmetic, `ec_mul2` into `pq = H`, `ec_to_affine(pq)`, the
public key written big-endian into `[Out, Out + 64)`, and the heap released to the mark `H`. -/
theorem srPost_wn (Lo Sc Out H : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0)
    (oO : ¬ MWin Out 64 w) (oH : ¬ MWin H 96 w) (hP0 : P0.toNat ≤ H.toNat) (hcapH : H.toNat ≤ 33806089496)
    (hal : H.toNat % 8 = 0) (hLoH : Lo.toNat ≤ H.toNat) {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => SRL Out H L ∧ RG Lo Sc G) Q
      (fun _ _ G => RG Lo Sc G) srPost := by
  unfold srPost
  have u := fun (n : MlS) (h1 : ofString "out" ≠ n) (h2 : ofString "mark" ≠ n) (h3 : ofString "pq" ≠ n) =>
    srl_upd (Out := Out) (H := H) n h1 h2 h3
  refine decR0 (LP := SRL Out H) (GP := RG Lo Sc) (ofString "rx") _ _ (u _ (by decide) (by decide) (by decide)) ?_
  refine decR0 (LP := SRL Out H) (GP := RG Lo Sc) (ofString "ry") _ _ (u _ (by decide) (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRL Out H) (ofString "e") _ _ _ _ _ _ originalRuntimeCode_u256FromBe_lookup
    (memoryFrame_of_good originalRuntimeCode_u256FromBe_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_u256_from_be) (by body_check Guest.guestFn_u256_from_be)
    (u _ (by decide) (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRL Out H) (ofString "elt") _ _ _ _ _ _ vmLookup_u256_lt
    (memoryFrame_of_good vmLookup_u256_lt (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt)
    (by body_check Guest.guestFn_u256_lt) (u _ (by decide) (by decide) (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (rcallMFS (LP := SRL Out H) (GP := RG Lo Sc) (ofString "e") _ _ _ _ _ vmLookup_u256_sub
    (memoryFrame_of_good vmLookup_u256_sub (by decide) (by decide)) (by body_check Guest.guestFn_u256_sub)
    (by body_check Guest.guestFn_u256_sub) (u _ (by decide) (by decide) (by decide))) aqgd_skip) ?_
  refine rdecU4 (GP := RG Lo Sc) (LP' := SRL Out H) (fun L => LU4 (ofString "a") L) (ofString "rinv") _ _ _ _ _ _
    originalRuntimeCode_fnInv_lookup (fnInv_wn Lo Sc hw out)
    (fun s values callee rs _ args lookup => entryS1 originalRuntimeCode_fnInv_lookup s _ args lookup)
    (fun L v lp _ => u _ (by decide) (by decide) (by decide) _ _ lp) ?_
  refine decR0 (LP := SRL Out H) (GP := RG Lo Sc) (ofString "nege") _ _ (u _ (by decide) (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRL Out H) (ofString "ez") _ _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero) (u _ (by decide) (by decide) (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (rcallMFS (LP := SRL Out H) (GP := RG Lo Sc) (ofString "nege") _ _ _ _ _
    vmLookup_u256_sub (memoryFrame_of_good vmLookup_u256_sub (by decide) (by decide))
    (by body_check Guest.guestFn_u256_sub) (by body_check Guest.guestFn_u256_sub)
    (u _ (by decide) (by decide) (by decide))) aqgd_skip) ?_
  refine rdecU4 (GP := RG Lo Sc) (LP' := SRL Out H) (fun L => LU4 (ofString "a") L ∧ LU4 (ofString "b") L)
    (ofString "u1") _ _ _ _ _ _ vmLookup_fn_mul (fnMulRG Lo Sc out)
    (fun s values callee rs _ args lookup => entryS2 vmLookup_fn_mul (by decide) s _ _ args lookup)
    (fun L v lp _ => u _ (by decide) (by decide) (by decide) _ _ lp) ?_
  refine rdecU4 (GP := RG Lo Sc) (LP' := SRL Out H) (fun L => LU4 (ofString "a") L ∧ LU4 (ofString "b") L)
    (ofString "u2") _ _ _ _ _ _ vmLookup_fn_mul (fnMulRG Lo Sc out)
    (fun s values callee rs _ args lookup => entryS2 vmLookup_fn_mul (by decide) s _ _ args lookup)
    (fun L v lp _ => u _ (by decide) (by decide) (by decide) _ _ lp) ?_
  have hpq : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), SRL Out H s.locals →
      EV s (.var .local (ofString "pq")) = some (.val (.word H)) := fun s h => by simp [EV,evalHOLExact,h.2.2]
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := SRL Out H) (Rv := fun _ => True) (EM0 H) _ _ _ _ _
    originalRuntimeCode_ecMul2_lookup
    (aqgd_conseq (ecMul2_wn Lo Sc H hw out hSc0 oH) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs lp args lookup => entry_em2S s _ _ _ _ _ _ _ H (hpq s lp) args lookup)) ?_
  refine rdecAny (GP := RG Lo Sc) (LP' := SRL Out H) (fun L => L.lookup (ofString "pt") = some (.val (.word H)))
    (ofString "ok") _ _ _ _ _ _ originalRuntimeCode_ecToAffine_lookup (ecToAffine_wn Lo Sc H hw out oH)
    (fun s values callee rs lp args lookup =>
      entry_pt originalRuntimeCode_ecToAffine_lookup s _ H (hpq s lp) args lookup)
    (fun L v lp => u _ (by decide) (by decide) (by decide) _ _ lp) ?_
  have hout : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), SRL Out H s.locals →
      s.locals.lookup (ofString "out") = some (.val (.word Out)) := fun s h => h.1
  refine aqgd_seq (aqgd_iteT _ ?_ aqgd_skip) ?_
  · refine decRK (LP := SRL Out H) (GP := RG Lo Sc) (ofString "qx") _ _ (u _ (by decide) (by decide) (by decide))
      (srl_res _ (by decide) (by decide) (by decide)) ?_
    refine decRK (LP := SRL Out H) (GP := RG Lo Sc) (ofString "qy") _ _ (u _ (by decide) (by decide) (by decide))
      (srl_res _ (by decide) (by decide) (by decide)) ?_
    refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := SRL Out H) (Rv := fun _ => True)
      (fun L => L.lookup (ofString "out") = some (.val (.word Out))) _ _ _ _ _ vmLookup_u256_to_be32
      (u2bRG Lo Sc Out (mwin_mono (by decide) oO))
      (fun s values callee rs lp args lookup => entry_u2b s _ _ Out (by simp [EV,evalHOLExact,hout s lp]) args lookup))
      ?_
    exact rcallK (GP := RG Lo Sc) (LP := SRL Out H) (Rv := fun _ => True)
      (fun L => L.lookup (ofString "out") = some (.val (.word (Out + 32#64)))) _ _ _ _ _ vmLookup_u256_to_be32
      (u2bRG Lo Sc (Out + 32#64) (mwin_shift oO 32 32 (by decide)))
      (fun s values callee rs lp args lookup => entry_u2b s _ _ _
        (by simp [EV,evalHOLExact,evalListHOLExact,hout s lp,wordOpHOL,wordOp,valueIsWord,valueWord]) args lookup)
  refine aqgd_seq (Q := fun _ _ G => HeapIs G H ∧ ScrIs Sc G) (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "m") = some (.val (.word H)) ∧ M = M0') ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (M' = M0' ∧ HeapIs G' H) ∧ OnlyHeap G0' G')
    _ _ _ _ _ originalRuntimeCode_heap_release_lookup (by simp)
    (fun _ M0' G0' _ => heapReleaseN_spec (SP0 := SP0) (G0 := G0) (FM := FM) (J := J) (C := C) (SKB := SKB) (Nj := Nj)
      (D := D) (B := B) (w := w) M0' H hP0 hcapH hal G0') ?_ ?_) (aqgd_return _ ?_)
  · intro F s values callee rs _ H' hG ⟨lp,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,lp.2.1] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_heap_release_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩,rfl⟩
  · intro L M G v M' G' ⟨_,rg⟩ ⟨⟨_,hH⟩,oh⟩
    exact ⟨hH,scrIs_onlyHeap oh rg.2⟩
  · intro F s v _ _ _ ⟨hH,hsc⟩ _ _
    exact ⟨⟨H,hH,hLoH⟩,hsc⟩

#print axioms srPost_wn

theorem entry_dcr {F : Type} (s : PanSemStateFiniteExact 64 F) (e0 e1 e2 : ExpHOL 64) (P : BitVec 64)
    (h2 : EV s e2 = some (.val (.word P))) {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA}
    {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e0,e1,e2] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "secp256k1_decompress_r") values =
      some (body,callee,rs)) : callee.lookup (ofString "out") = some (.val (.word P)) := by
  obtain ⟨v0,vs,rfl,_,r0⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v1,vs1,rfl,_,r1⟩ := evalList_cons' s _ _ _ r0
  obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  rw [h2] at ev2; simp only [Option.some.injEq] at ev2; subst ev2
  have e := callee_eq originalRuntimeCode_secp256k1DecompressR_lookup lookup
  rw [e]; simp (config := {decide := true})

/-- `secp256k1_recover` from the heap mark: `pq = alloc(96)` at `H`, `pr = alloc(96)` above it, the decompression into
`pr`, then `srPost`. -/
theorem srMid_wn (Lo Sc Out H : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0)
    (oO : ¬ MWin Out 64 w) (hP0 : P0.toNat ≤ H.toNat) (hcapH : H.toNat ≤ 33806089496) (hal : H.toNat % 8 = 0)
    (hLoH : Lo.toNat ≤ H.toNat) {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "out") = some (.val (.word Out)) ∧ HeapIs G H) ∧ ScrIs Sc G) Q
      (fun _ _ G => RG Lo Sc G) srMid := by
  unfold srMid
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      v = .val (.word H) ∧ M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => ((L.lookup (ofString "out") = some (.val (.word Out)) ∧
      L.lookup (ofString "mark") = some (.val (.word H))) ∧ HeapIs G H) ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_heap_mark_lookup
    (fun _ M0' G0' ⟨⟨_,hH⟩,_⟩ => heapMark_spec M0' G0' H hH) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨ho,hH⟩,hsc⟩ ⟨ev,_,hG⟩ _
    subst ev hG
    exact ⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ho,lookup_update_eq' _ _ _⟩,hH⟩,hsc⟩
  -- pq = alloc(96)
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 96#64)) ∧ M = M0' ∧ HeapIs G H) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + (96#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => SRL Out H L ∧ (∃ H1 : BitVec 64, HeapIs G H1 ∧ H.toNat + 96 ≤ H1.toNat) ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) 96#64 H M0' G0') ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H' hG ⟨⟨_,hH⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hH⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨ho,hm⟩,_⟩,hsc⟩ ⟨⟨ev,_,H',hH',c1,_⟩,oh⟩ _
    subst ev
    have : (96#64).toNat = 96 := rfl
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ho,by rw [lookup_update_ne' _ _ (by decide)]; exact hm,
      lookup_update_eq' _ _ _⟩,⟨H',hH',by omega⟩,scrIs_onlyHeap oh hsc⟩
  -- fix the heap pointer H1 for pr
  refine aqgd_conseq (P := fun L _ G => ∃ H1 : BitVec 64, (SRL Out H L ∧ HeapIs G H1 ∧ H.toNat + 96 ≤ H1.toNat) ∧
      ScrIs Sc G) (Q := fun _ _ _ => False) ?_
    (fun _ _ _ ⟨h,⟨H1,hH,le⟩,hsc⟩ => ⟨H1,⟨h,hH,le⟩,hsc⟩) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  refine aqgd_exE (fun H1 => ?_)
  refine aqgd_of_arenaFact (Φ := (P0.toNat ≤ H1.toNat ∧ H1.toNat ≤ 33806089496 ∧ H1.toNat % 8 = 0) ∧
    H.toNat + 96 ≤ H1.toNat) (fun _ _ g aw ⟨⟨_,hH,le⟩,_⟩ => ⟨jws_heap_facts aw.1 hH,le⟩) ?_
  intro ⟨⟨_,hcap1,hal1⟩,hle1⟩
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 96#64)) ∧ M = M0' ∧ HeapIs G H1) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H1) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H1.toNat + (96#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => ((SRL Out H L ∧ L.lookup (ofString "pr") = some (.val (.word H1))) ∧ RG Lo Sc G) ∧
      H1.toNat + 96 ≤ 33806089496)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) 96#64 H1 M0' G0') ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H' hG ⟨⟨_,hH,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hH⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨srl,_,_⟩,hsc⟩ ⟨⟨ev,_,H',hH',c1,c2⟩,oh⟩ _
    subst ev
    have : (96#64).toNat = 96 := rfl
    exact ⟨⟨⟨srl_upd _ (by decide) (by decide) (by decide) _ _ srl,lookup_update_eq' _ _ _⟩,
      ⟨H',hH',by omega⟩,scrIs_onlyHeap oh hsc⟩,by omega⟩
  refine aqgd_pureE (fun hcap1' => ?_)
  have oH1 : ¬ MWin H1 96 w := by simpa using mwin_aboveH (k := 0) hal1 (by omega) (by omega)
  have oH : ¬ MWin H 96 w := by simpa using mwin_aboveH (k := 0) hal (by omega) (by omega)
  let SR1 := fun L : GA => SRL Out H L ∧ L.lookup (ofString "pr") = some (.val (.word H1))
  refine rdecAny (GP := RG Lo Sc) (LP := SR1) (LP' := SRL Out H)
    (fun L => L.lookup (ofString "out") = some (.val (.word H1))) (ofString "okr") _ _ _ _ _ _
    originalRuntimeCode_secp256k1DecompressR_lookup (decompress_wn Lo Sc H1 hw out oH1)
    (fun s values callee rs lp args lookup => entry_dcr s _ _ _ H1 (by simp [EV,evalHOLExact,lp.2]) args lookup)
    (fun L v lp => srl_upd _ (by decide) (by decide) (by decide) _ _ lp.1) ?_
  refine aqgd_seq (aqgd_iteT _ ?_ aqgd_skip) (srPost_wn Lo Sc Out H hw out hSc0 oO oH hP0 hcapH hal hLoH)
  refine aqgd_seq (Q := fun _ _ G => HeapIs G H ∧ ScrIs Sc G) (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "m") = some (.val (.word H)) ∧ M = M0') ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (M' = M0' ∧ HeapIs G' H) ∧ OnlyHeap G0' G')
    _ _ _ _ _ originalRuntimeCode_heap_release_lookup (by simp)
    (fun _ M0' G0' _ => heapReleaseN_spec (SP0 := SP0) (G0 := G0) (FM := FM) (J := J) (C := C) (SKB := SKB) (Nj := Nj)
      (D := D) (B := B) (w := w) M0' H hP0 hcapH hal G0') ?_ ?_) (aqgd_return _ ?_)
  · intro F s values callee rs _ H' hG ⟨lp,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,lp.2.1] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_heap_release_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩,rfl⟩
  · intro L M G v M' G' ⟨_,rg⟩ ⟨⟨_,hH⟩,oh⟩
    exact ⟨hH,scrIs_onlyHeap oh rg.2⟩
  · intro F s v _ _ _ ⟨hH,hsc⟩ _ _
    exact ⟨⟨H,hH,hLoH⟩,hsc⟩

#print axioms srMid_wn

/-- The actual `secp256k1_recover(msg_hash, r, s, recid, out)`: writes only the public key `[Out, Out + 64)`, the
accelerator scratch and heap blocks above the heap fence (released); keeps `RG`. -/
theorem secpRecover_wn (Lo Sc Out : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0)
    (oO : ¬ MWin Out 64 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word Out)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_secp256k1_recover) := by
  rw [srTop_eq]; unfold srTop
  let SO := fun L : GA => L.lookup (ofString "out") = some (.val (.word Out))
  have hu : ∀ (n : MlS), ofString "out" ≠ n → ∀ L v, SO L → SO (L.update (n,v)) :=
    fun n h L v hp => by show _ = _; rw [lookup_update_ne' _ _ h]; exact hp
  refine rdecMF (LP' := SO) (ofString "rz") _ _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero) (hu _ (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (retRG Lo Sc _) aqgd_skip) ?_
  refine rdecMF (LP' := SO) (ofString "rlt") _ _ _ _ _ _ vmLookup_u256_lt
    (memoryFrame_of_good vmLookup_u256_lt (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt)
    (by body_check Guest.guestFn_u256_lt) (hu _ (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (retRG Lo Sc _) aqgd_skip) ?_
  refine rdecMF (LP' := SO) (ofString "sz") _ _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero) (hu _ (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (retRG Lo Sc _) aqgd_skip) ?_
  refine rdecMF (LP' := SO) (ofString "slt") _ _ _ _ _ _ vmLookup_u256_lt
    (memoryFrame_of_good vmLookup_u256_lt (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt)
    (by body_check Guest.guestFn_u256_lt) (hu _ (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (retRG Lo Sc _) aqgd_skip) ?_
  refine aqgd_conseq (P := fun L _ G => ∃ H : BitVec 64, ((SO L ∧ HeapIs G H) ∧ ScrIs Sc G) ∧ Lo.toNat ≤ H.toNat)
    (Q := fun _ _ _ => False) ?_ (fun _ _ _ ⟨h,⟨H,hH,le⟩,hsc⟩ => ⟨H,⟨⟨h,hH⟩,hsc⟩,le⟩) (fun _ _ _ h => h.elim)
    (fun _ _ _ h => h)
  refine aqgd_exE (fun H => ?_)
  refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
    (fun _ _ g aw ⟨⟨⟨_,hH⟩,_⟩,_⟩ => jws_heap_facts aw.1 hH) ?_
  intro ⟨hP0,hcapH,hal⟩
  exact aqgd_pureE (fun hLoH => srMid_wn Lo Sc Out H hw out hSc0 oO hP0 hcapH hal hLoH)

#print axioms secpRecover_wn
end u2
end InitECandidate.Runtime
