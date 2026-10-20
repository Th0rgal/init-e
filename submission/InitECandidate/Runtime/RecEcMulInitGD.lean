import InitECandidate.Runtime.RecEcAddGD
/-!
`ec_mul2` split into `emTop` / `emInit K` / `emTail` / `emLoopBody`; table-call rules (`tcInf`, `tcDbl`, `tcSA`,
`tcAA`) and the 31 table-initialisation calls (`emInit_wn`): every point written lies in the fresh table above the
heap fence.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def emLoopBody : ProgHOL 64 :=
  (.seq (.assign .local (ofString "win") (.op .sub [(.var .local (ofString "win")),(.const 1)])) (.seq (.call (some (none,none)) (ofString "ec_double") [(.var .local (ofString "out"))]) (.seq (.call (some (none,none)) (ofString "ec_double") [(.var .local (ofString "out"))]) (.dec (ofString "pos") .one (.panop .mul [(.var .local (ofString "win")),(.const 2)]) (.decCall (ofString "high1") .one (ofString "u256_bit") [(.var .local (ofString "k1")),(.op .add [(.var .local (ofString "pos")),(.const 1)])] (.dec (ofString "wd1") .one (.panop .mul [(.var .local (ofString "high1")),(.const 2)]) (.decCall (ofString "low1") .one (ofString "u256_bit") [(.var .local (ofString "k1")),(.var .local (ofString "pos"))] (.seq (.assign .local (ofString "wd1") (.op .add [(.var .local (ofString "wd1")),(.var .local (ofString "low1"))])) (.decCall (ofString "high2") .one (ofString "u256_bit") [(.var .local (ofString "k2")),(.op .add [(.var .local (ofString "pos")),(.const 1)])] (.dec (ofString "wd2") .one (.panop .mul [(.var .local (ofString "high2")),(.const 2)]) (.decCall (ofString "low2") .one (ofString "u256_bit") [(.var .local (ofString "k2")),(.var .local (ofString "pos"))] (.seq (.assign .local (ofString "wd2") (.op .add [(.var .local (ofString "wd2")),(.var .local (ofString "low2"))])) (.dec (ofString "digit") .one (.op .add [(.panop .mul [(.var .local (ofString "wd1")),(.const 4)]),(.var .local (ofString "wd2"))]) (.ite (.cmp .notEqual (.var .local (ofString "digit")) (.const 0)) (.dec (ofString "entry") .one (.op .add [(.var .local (ofString "table")),(.panop .mul [(.var .local (ofString "digit")),(.const 96)])]) (.decCall (ofString "entry_inf") .one (ofString "ec_is_infinity") [(.var .local (ofString "entry"))] (.ite (.cmp .equal (.var .local (ofString "entry_inf")) (.const 0)) (.call (some (none,none)) (ofString "ec_add_affine") [(.var .local (ofString "out")),(.load (.comb [.one,.one,.one,.one]) (.var .local (ofString "entry"))),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "entry")),(.const 32)]))]) .skip))) .skip))))))))))))))

def emTail : ProgHOL 64 :=
  (.dec (ofString "win") .one (.const 128) (.seq (.while (.cmp .lower (.const 0) (.var .local (ofString "win"))) emLoopBody) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.const 0)))))

def emInit (K : ProgHOL 64) : ProgHOL 64 :=
  (.seq (.call (some (none,none)) (ofString "ec_set_infinity") [(.var .local (ofString "table"))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 4),(.const 96)])]),(.var .local (ofString "ax")),(.var .local (ofString "ay"))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 8),(.const 96)])]),(.var .local (ofString "ax")),(.var .local (ofString "ay"))]) (.seq (.call (some (none,none)) (ofString "ec_double") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 8),(.const 96)])])]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 12),(.const 96)])]),(.var .local (ofString "ax")),(.var .local (ofString "ay"))]) (.seq (.call (some (none,none)) (ofString "ec_double") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 12),(.const 96)])])]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 12),(.const 96)])]),(.var .local (ofString "ax")),(.var .local (ofString "ay"))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.const 96)]),(.var .local (ofString "bx")),(.var .local (ofString "by"))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 2),(.const 96)])]),(.var .local (ofString "bx")),(.var .local (ofString "by"))]) (.seq (.call (some (none,none)) (ofString "ec_double") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 2),(.const 96)])])]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 3),(.const 96)])]),(.var .local (ofString "bx")),(.var .local (ofString "by"))]) (.seq (.call (some (none,none)) (ofString "ec_double") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 3),(.const 96)])])]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 3),(.const 96)])]),(.var .local (ofString "bx")),(.var .local (ofString "by"))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 5),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 4),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 4),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 5),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.const 96)])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.const 96),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 6),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 4),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 4),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 6),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 2),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 2),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 7),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 4),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 4),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 7),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 3),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 3),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 9),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 8),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 8),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 9),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.const 96)])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.const 96),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 10),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 8),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 8),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 10),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 2),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 2),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 11),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 8),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 8),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 11),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 3),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 3),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 13),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 12),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 12),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 13),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.const 96)])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.const 96),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 14),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 12),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 12),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 14),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 2),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 2),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_set_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 15),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 12),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 12),(.const 96)]),(.const 32)]))]) (.seq (.call (some (none,none)) (ofString "ec_add_affine") [(.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 15),(.const 96)])]),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 3),(.const 96)])])),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.const 3),(.const 96)]),(.const 32)]))]) K)))))))))))))))))))))))))))))))

def emTop : ProgHOL 64 :=
  (.seq (.call (some (none,none)) (ofString "ec_set_infinity") [(.var .local (ofString "out"))]) (.decCall (ofString "len1") .one (ofString "u256_bit_length") [(.var .local (ofString "k1"))] (.decCall (ofString "len2") .one (ofString "u256_bit_length") [(.var .local (ofString "k2"))] (.decCall (ofString "i") .one (ofString "max") [(.var .local (ofString "len1")),(.var .local (ofString "len2"))] (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.const 0)) (.return (.const 0)) .skip) (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "table") .one (ofString "alloc") [(.panop .mul [(.const 16),(.const 96)])] (emInit emTail))))))))

theorem emTop_eq : sourceFunctionBody Guest.guestFn_ec_mul2 = emTop := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_ec_mul2,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- Locals of `ec_mul2` after the table allocation. -/
def TB (H Out : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "out") = some (.val (.word Out)) ∧ L.lookup (ofString "table") = some (.val (.word H)) ∧
    L.lookup (ofString "mark") = some (.val (.word H)) ∧ LU4 (ofString "ax") L ∧ LU4 (ofString "ay") L ∧
    LU4 (ofString "bx") L ∧ LU4 (ofString "by") L

theorem mwin_aboveH {H w : BitVec 64} {k n : Nat} (hal : H.toNat % 8 = 0) (hw : w.toNat < H.toNat)
    (hk : H.toNat + k + n < 2 ^ 64) : ¬ MWin (H + BitVec.ofNat 64 k) n w := by
  rintro ⟨j,hj,e | e⟩
  · have : (H + BitVec.ofNat 64 k + BitVec.ofNat 64 j).toNat = H.toNat + k + j := by
      simp [BitVec.toNat_add]; omega
    rw [← e] at this; omega
  · have h1 := align_toNat (H + BitVec.ofNat 64 k + BitVec.ofNat 64 j)
    have : (H + BitVec.ofNat 64 k + BitVec.ofNat 64 j).toNat = H.toNat + k + j := by
      simp [BitVec.toNat_add]; omega
    rw [this,← e] at h1; omega

theorem entry_eaa {F : Type} (s : PanSemStateFiniteExact 64 F) (e0 : ExpHOL 64) (Pt : BitVec 64)
    (h0 : EV s e0 = some (.val (.word Pt))) (e1 e2 : ExpHOL 64)
    (h1 : ∀ v, EV s e1 = some v → U4V v) (h2 : ∀ v, EV s e2 = some v → U4V v)
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e0,e1,e2] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ec_add_affine") values = some (body,callee,rs)) :
    EA0 Pt callee := by
  obtain ⟨v0,vs,rfl,ev0,r0⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v1,vs1,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ r0
  obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  rw [h0] at ev0; simp only [Option.some.injEq] at ev0; subst ev0
  have e := callee_eq originalRuntimeCode_ecAddAffine_lookup lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),⟨v1,by rw [e]; simp (config := {decide := true}),h1 _ ev1⟩,
    ⟨v2,by rw [e]; simp (config := {decide := true}),h2 _ ev2⟩⟩

section tc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {RR : ValueHOL 64 → Mem → GA → Prop} {LP : GA → Prop}

theorem tcInf (Lo Sc : BitVec 64) {P : BitVec 64} (k : Nat) (hP : ¬ MWin P 96 w) (e : ExpHOL 64)
    (hev : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → EV s e = some (.val (.word P))) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ RG Lo Sc G)
      (fun L _ G => LP L ∧ RG Lo Sc G) RR (.call (some (none,none)) (ofString "ec_set_infinity") [e]) :=
  rcallK (GP := RG Lo Sc) (LP := LP) (fun L => L.lookup (ofString "pt") = some (.val (.word P))) _ _ _ _ _
    vmLookup_ec_set_infinity (ecSetInfRG Lo Sc P hP)
    (fun s values callee rs lp args lookup => entry_pt vmLookup_ec_set_infinity s e P (hev s lp) args lookup)

theorem tcDbl (Lo Sc : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) {P : BitVec 64} (k : Nat)
    (hP : ¬ MWin P 96 w) (e : ExpHOL 64)
    (hev : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → EV s e = some (.val (.word P))) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ RG Lo Sc G)
      (fun L _ G => LP L ∧ RG Lo Sc G) RR (.call (some (none,none)) (ofString "ec_double") [e]) :=
  rcallK (GP := RG Lo Sc) (LP := LP) (Rv := fun _ => True) (fun L => L.lookup (ofString "pt") = some (.val (.word P)))
    _ _ _ _ _ originalRuntimeCode_ecDouble_lookup
    (aqgd_conseq (ecDouble_wn Lo Sc P hw out hP) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs lp args lookup => entry_pt originalRuntimeCode_ecDouble_lookup s e P (hev s lp) args lookup)

theorem tcSA (Lo Sc : BitVec 64) {P : BitVec 64} (k : Nat) (hP : ¬ MWin P 96 w) (e : ExpHOL 64)
    (hev : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → EV s e = some (.val (.word P)))
    (e1 e2 : ExpHOL 64)
    (h1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∀ v, EV s e1 = some v → U4V v)
    (h2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∀ v, EV s e2 = some v → U4V v) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ RG Lo Sc G)
      (fun L _ G => LP L ∧ RG Lo Sc G) RR (.call (some (none,none)) (ofString "ec_set_affine") [e,e1,e2]) :=
  rcallK (GP := RG Lo Sc) (LP := LP)
    (fun L => L.lookup (ofString "pt") = some (.val (.word P)) ∧ LU4 (ofString "x") L ∧ LU4 (ofString "y") L)
    _ _ _ _ _ vmLookup_ec_set_affine (ecSetAffineRG Lo Sc P hP)
    (fun s values callee rs lp args lookup => entry_esa s e P (hev s lp) e1 e2 (h1 s lp) (h2 s lp) args lookup)

theorem tcAA (Lo Sc : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0) {P : BitVec 64}
    (k : Nat) (hP : ¬ MWin P 96 w) (e : ExpHOL 64)
    (hev : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → EV s e = some (.val (.word P)))
    (e1 e2 : ExpHOL 64)
    (h1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∀ v, EV s e1 = some v → U4V v)
    (h2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∀ v, EV s e2 = some v → U4V v) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ RG Lo Sc G)
      (fun L _ G => LP L ∧ RG Lo Sc G) RR (.call (some (none,none)) (ofString "ec_add_affine") [e,e1,e2]) :=
  rcallK (GP := RG Lo Sc) (LP := LP) (Rv := fun _ => True) (EA0 P) _ _ _ _ _ originalRuntimeCode_ecAddAffine_lookup
    (aqgd_conseq (ecAddAffine_wn Lo Sc P hw out hSc0 hP) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs lp args lookup => entry_eaa s e P (hev s lp) e1 e2 (h1 s lp) (h2 s lp) args lookup)

#print axioms tcAA

/-- The 31 table-initialisation calls of `ec_mul2`: every point written is `table + 96 k`, `k < 16`, inside the fresh
table above the heap fence. -/
theorem emInit_wn (Lo Sc H Out : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0)
    (hal : H.toNat % 8 = 0) (hwH : w.toNat < H.toNat) (hcap : H.toNat + 1536 ≤ 33806089496)
    {K : ProgHOL 64} {Q : GA → Mem → GA → Prop}
    (hK : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => TB H Out L ∧ RG Lo Sc G) Q RR K) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => TB H Out L ∧ RG Lo Sc G) Q RR
      (emInit K) := by
  have hwin : ∀ k : Nat, 96 * k + 96 ≤ 1536 → ¬ MWin (H + BitVec.ofNat 64 (96 * k)) 96 w :=
    fun k hk => mwin_aboveH hal hwH (by omega)
  unfold emInit
  refine aqgd_seq (tcInf (LP := TB H Out) Lo Sc 0 (hwin 0 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL])) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 4 (hwin 4 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s tb => ev_var_u4v s _ tb.2.2.2.1) (fun s tb => ev_var_u4v s _ tb.2.2.2.2.1)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 8 (hwin 8 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s tb => ev_var_u4v s _ tb.2.2.2.1) (fun s tb => ev_var_u4v s _ tb.2.2.2.2.1)) ?_
  refine aqgd_seq (tcDbl (LP := TB H Out) Lo Sc hw out 8 (hwin 8 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL])) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 12 (hwin 12 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s tb => ev_var_u4v s _ tb.2.2.2.1) (fun s tb => ev_var_u4v s _ tb.2.2.2.2.1)) ?_
  refine aqgd_seq (tcDbl (LP := TB H Out) Lo Sc hw out 12 (hwin 12 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL])) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 12 (hwin 12 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s tb => ev_var_u4v s _ tb.2.2.2.1) (fun s tb => ev_var_u4v s _ tb.2.2.2.2.1)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 1 (hwin 1 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s tb => ev_var_u4v s _ tb.2.2.2.2.2.1) (fun s tb => ev_var_u4v s _ tb.2.2.2.2.2.2)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 2 (hwin 2 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s tb => ev_var_u4v s _ tb.2.2.2.2.2.1) (fun s tb => ev_var_u4v s _ tb.2.2.2.2.2.2)) ?_
  refine aqgd_seq (tcDbl (LP := TB H Out) Lo Sc hw out 2 (hwin 2 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL])) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 3 (hwin 3 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s tb => ev_var_u4v s _ tb.2.2.2.2.2.1) (fun s tb => ev_var_u4v s _ tb.2.2.2.2.2.2)) ?_
  refine aqgd_seq (tcDbl (LP := TB H Out) Lo Sc hw out 3 (hwin 3 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL])) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 3 (hwin 3 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s tb => ev_var_u4v s _ tb.2.2.2.2.2.1) (fun s tb => ev_var_u4v s _ tb.2.2.2.2.2.2)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 5 (hwin 5 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 5 (hwin 5 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 6 (hwin 6 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 6 (hwin 6 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 7 (hwin 7 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 7 (hwin 7 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 9 (hwin 9 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 9 (hwin 9 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 10 (hwin 10 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 10 (hwin 10 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 11 (hwin 11 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 11 (hwin 11 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 13 (hwin 13 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 13 (hwin 13 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 14 (hwin 14 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 14 (hwin 14 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcSA (LP := TB H Out) Lo Sc 15 (hwin 15 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  refine aqgd_seq (tcAA (LP := TB H Out) Lo Sc hw out hSc0 15 (hwin 15 (by omega)) _ (fun s tb => by simp [EV,evalHOLExact,evalListHOLExact,tb.2.1,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]) _ _ (fun s _ v ev => ev_load_u4 s _ v ev) (fun s _ v ev => ev_load_u4 s _ v ev)) ?_
  exact hK

#print axioms emInit_wn
end tc
end InitECandidate.Runtime
