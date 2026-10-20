import InitECandidate.Runtime.RecSigHashGD
import InitECandidate.Runtime.VmFn_u256_add
import InitECandidate.Runtime.VmFn_u256_gt
import InitECandidate.Runtime.VmFn_u256_fits_word
/-!
Window specs of the actual `signing_hash_*` tail calls and `signature_recovery_parameters(tx, chain_id, out_hash)` (split
`srpTop` / `srpTail` / `srpT0`): the only writes are the signing hash into `[O, O + 32)`, the static Keccak buffers,
and released heap above the fence.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def sh155Body : ProgHOL 64 :=
  (.call none (ofString "tx_signing_hash_mode") [(.var .local (ofString "tx")),(.const 2),(.var .local (ofString "chain_id")),(.var .local (ofString "out"))])

theorem sh155Body_eq : sourceFunctionBody Guest.guestFn_signing_hash_155 = sh155Body := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_signing_hash_155,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def shPreBody : ProgHOL 64 :=
  (.call none (ofString "tx_signing_hash_mode") [(.var .local (ofString "tx")),(.const 1),(.const 0),(.var .local (ofString "out"))])

theorem shPreBody_eq : sourceFunctionBody Guest.guestFn_signing_hash_pre155 = shPreBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_signing_hash_pre155,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def sh2930Body : ProgHOL 64 :=
  (.call none (ofString "tx_signing_hash_mode") [(.var .local (ofString "tx")),(.const 1),(.const 0),(.var .local (ofString "out"))])

theorem sh2930Body_eq : sourceFunctionBody Guest.guestFn_signing_hash_2930 = sh2930Body := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_signing_hash_2930,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def sh1559Body : ProgHOL 64 :=
  (.call none (ofString "tx_signing_hash_mode") [(.var .local (ofString "tx")),(.const 1),(.const 0),(.var .local (ofString "out"))])

theorem sh1559Body_eq : sourceFunctionBody Guest.guestFn_signing_hash_1559 = sh1559Body := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_signing_hash_1559,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def sh4844Body : ProgHOL 64 :=
  (.call none (ofString "tx_signing_hash_mode") [(.var .local (ofString "tx")),(.const 1),(.const 0),(.var .local (ofString "out"))])

theorem sh4844Body_eq : sourceFunctionBody Guest.guestFn_signing_hash_4844 = sh4844Body := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_signing_hash_4844,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

def sh7702Body : ProgHOL 64 :=
  (.call none (ofString "tx_signing_hash_mode") [(.var .local (ofString "tx")),(.const 1),(.const 0),(.var .local (ofString "out"))])

theorem sh7702Body_eq : sourceFunctionBody Guest.guestFn_signing_hash_7702 = sh7702Body := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_signing_hash_7702,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl


section st
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat} {LP : GA → Prop}

/-- A tail call `tx_signing_hash_mode(tx, e2, e3, out)` with `e3` word-valued and `out = O`. -/
theorem shTail_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) (e2 e3 : ExpHOL 64)
    (h3 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∃ c : BitVec 64, EV s e3 = some (.val (.word c)))
    (ho : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      s.locals.lookup (ofString "out") = some (.val (.word O))) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun _ _ G => RG Lo Sc G)
      (.call none (ofString "tx_signing_hash_mode") [.var .local (ofString "tx"),e2,e3,.var .local (ofString "out")]) :=
  aqgd_tailCallSpecS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ G => (L.lookup (ofString "out") = some (.val (.word O)) ∧
      ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))) ∧ RG Lo Sc G)
    (RRe := fun _ _ _ _ _ G => RG Lo Sc G) _ _ _ _ _ originalRuntimeCode_txSigningHashMode_lookup
    (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ => sigHashMode_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO)
    (fun s values callee rs _ H hG ⟨lp,rg⟩ _ args lookup => by
      unfold GIs at hG; subst hG
      obtain ⟨c,hc⟩ := h3 s lp
      obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      obtain ⟨v4,vs4,rfl,ev4,r4⟩ := evalList_cons' s _ _ _ r3
      have := evalList_nil' s _ r4; subst this
      rw [hc] at ev3; simp only [Option.some.injEq] at ev3; subst ev3
      simp [EV,evalHOLExact,ho s lp] at ev4; subst ev4
      have e := callee_eq originalRuntimeCode_txSigningHashMode_lookup lookup
      exact ⟨⟨by rw [e]; simp (config := {decide := true}),c,by rw [e]; simp (config := {decide := true})⟩,rg⟩)
    (fun _ _ _ _ _ _ _ h => h)

#print axioms shTail_wn

theorem shPre_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word O)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_signing_hash_pre155) := by
  rw [shPreBody_eq]; unfold shPreBody
  exact shTail_wn (LP := fun L => L.lookup (ofString "out") = some (.val (.word O))) hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw
    oK oP oO _ _ (fun s _ => ⟨0,by simp [EV,evalHOLExact]⟩) (fun s h => h)

theorem sh2930_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word O)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_signing_hash_2930) := by
  rw [sh2930Body_eq]; unfold sh2930Body
  exact shTail_wn (LP := fun L => L.lookup (ofString "out") = some (.val (.word O))) hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw
    oK oP oO _ _ (fun s _ => ⟨0,by simp [EV,evalHOLExact]⟩) (fun s h => h)

theorem sh1559_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word O)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_signing_hash_1559) := by
  rw [sh1559Body_eq]; unfold sh1559Body
  exact shTail_wn (LP := fun L => L.lookup (ofString "out") = some (.val (.word O))) hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw
    oK oP oO _ _ (fun s _ => ⟨0,by simp [EV,evalHOLExact]⟩) (fun s h => h)

theorem sh4844_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word O)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_signing_hash_4844) := by
  rw [sh4844Body_eq]; unfold sh4844Body
  exact shTail_wn (LP := fun L => L.lookup (ofString "out") = some (.val (.word O))) hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw
    oK oP oO _ _ (fun s _ => ⟨0,by simp [EV,evalHOLExact]⟩) (fun s h => h)

theorem sh7702_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word O)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_signing_hash_7702) := by
  rw [sh7702Body_eq]; unfold sh7702Body
  exact shTail_wn (LP := fun L => L.lookup (ofString "out") = some (.val (.word O))) hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw
    oK oP oO _ _ (fun s _ => ⟨0,by simp [EV,evalHOLExact]⟩) (fun s h => h)

theorem sh155_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "out") = some (.val (.word O)) ∧
        ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_signing_hash_155) := by
  rw [sh155Body_eq]; unfold sh155Body
  exact shTail_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO _ _
    (fun s ⟨_,c,hc⟩ => ⟨c,by simp [EV,evalHOLExact,hc]⟩) (fun s h => h.1)

#print axioms sh155_wn
end st

def srpT0 : ProgHOL 64 :=
  (.seq (.ite (.cmp .notEqual (.var .local (ofString "fits")) (.const 0)) (.ite (.cmp .notEqual (.const 0) (.op .or [(.cmp .equal (.rfield 0 (.var .local (ofString "v"))) (.const 27)),(.cmp .equal (.rfield 0 (.var .local (ofString "v"))) (.const 28))])) (.seq (.call (some (none,none)) (ofString "signing_hash_pre155") [(.var .local (ofString "tx")),(.var .local (ofString "out_hash"))]) (.return (.op .sub [(.rfield 0 (.var .local (ofString "v"))),(.const 27)]))) .skip) .skip) (.dec (ofString "c") (.comb [.one,.one,.one,.one]) (.rstruct [(.var .local (ofString "chain_id")),(.const 0),(.const 0),(.const 0)]) (.decCall (ofString "x2") (.comb [.one,.one,.one,.one]) (ofString "u256_add") [(.var .local (ofString "c")),(.var .local (ofString "c"))] (.decCall (ofString "v35") (.comb [.one,.one,.one,.one]) (ofString "u256_add") [(.var .local (ofString "x2")),(.rstruct [(.const 35),(.const 0),(.const 0),(.const 0)])] (.decCall (ofString "v36") (.comb [.one,.one,.one,.one]) (ofString "u256_add") [(.var .local (ofString "x2")),(.rstruct [(.const 36),(.const 0),(.const 0),(.const 0)])] (.decCall (ofString "eq35") .one (ofString "u256_eq") [(.var .local (ofString "v")),(.var .local (ofString "v35"))] (.decCall (ofString "eq36") .one (ofString "u256_eq") [(.var .local (ofString "v")),(.var .local (ofString "v36"))] (.seq (.ite (.op .and [(.cmp .notEqual (.const 0) (.cmp .equal (.var .local (ofString "eq35")) (.const 0))),(.cmp .notEqual (.const 0) (.cmp .equal (.var .local (ofString "eq36")) (.const 0)))]) (.raise (ofString "TxErr") (.const 42)) .skip) (.seq (.call (some (none,none)) (ofString "signing_hash_155") [(.var .local (ofString "tx")),(.var .local (ofString "chain_id")),(.var .local (ofString "out_hash"))]) (.return (.var .local (ofString "eq36"))))))))))))

def srpTail : ProgHOL 64 :=
  (.dec (ofString "t") .one (.load .one (.op .add [(.var .local (ofString "tx")),(.const 0)])) (.dec (ofString "v") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "tx")),(.const 288)])) (.decCall (ofString "fits") .one (ofString "u256_fits_word") [(.var .local (ofString "v"))] (.seq (.ite (.cmp .equal (.var .local (ofString "t")) (.const 0)) srpT0 .skip) (.seq (.ite (.cmp .equal (.var .local (ofString "fits")) (.const 0)) (.raise (ofString "TxErr") (.const 43)) .skip) (.seq (.ite (.cmp .lower (.const 1) (.rfield 0 (.var .local (ofString "v")))) (.raise (ofString "TxErr") (.const 43)) .skip) (.seq (.ite (.cmp .equal (.var .local (ofString "t")) (.const 1)) (.call (some (none,none)) (ofString "signing_hash_2930") [(.var .local (ofString "tx")),(.var .local (ofString "out_hash"))]) .skip) (.seq (.ite (.cmp .equal (.var .local (ofString "t")) (.const 2)) (.call (some (none,none)) (ofString "signing_hash_1559") [(.var .local (ofString "tx")),(.var .local (ofString "out_hash"))]) .skip) (.seq (.ite (.cmp .equal (.var .local (ofString "t")) (.const 3)) (.call (some (none,none)) (ofString "signing_hash_4844") [(.var .local (ofString "tx")),(.var .local (ofString "out_hash"))]) .skip) (.seq (.ite (.cmp .equal (.var .local (ofString "t")) (.const 4)) (.call (some (none,none)) (ofString "signing_hash_7702") [(.var .local (ofString "tx")),(.var .local (ofString "out_hash"))]) .skip) (.return (.rfield 0 (.var .local (ofString "v"))))))))))))))

def srpTop : ProgHOL 64 :=
  (.dec (ofString "r") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "tx")),(.const 320)])) (.dec (ofString "s") (.comb [.one,.one,.one,.one]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "tx")),(.const 352)])) (.decCall (ofString "z") .one (ofString "u256_is_zero") [(.var .local (ofString "r"))] (.seq (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0)) (.raise (ofString "TxErr") (.const 40)) .skip) (.decCall (ofString "lt") .one (ofString "u256_lt") [(.var .local (ofString "r")),(.rstruct [(.const 13822214165235122497),(.const 13451932020343611451),(.const 18446744073709551614),(.const 18446744073709551615)])] (.seq (.ite (.cmp .equal (.var .local (ofString "lt")) (.const 0)) (.raise (ofString "TxErr") (.const 40)) .skip) (.seq (.call (some ((some (.local,ofString "z")),none)) (ofString "u256_is_zero") [(.var .local (ofString "s"))]) (.seq (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0)) (.raise (ofString "TxErr") (.const 41)) .skip) (.decCall (ofString "gt") .one (ofString "u256_gt") [(.var .local (ofString "s")),(.rstruct [(.const 16134479119472337056),(.const 6725966010171805725),(.const 18446744073709551615),(.const 9223372036854775807)])] (.seq (.ite (.cmp .notEqual (.var .local (ofString "gt")) (.const 0)) (.raise (ofString "TxErr") (.const 41)) .skip) srpTail))))))))))

theorem srpTop_eq : sourceFunctionBody Guest.guestFn_signature_recovery_parameters = srpTop := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_signature_recovery_parameters,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- Locals of `signature_recovery_parameters`: the hash output and a word chain id. -/
def SRP (O : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "out_hash") = some (.val (.word O)) ∧
    ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))

theorem srp_upd {O : BitVec 64} (n : MlS) (h1 : ofString "out_hash" ≠ n) (h2 : ofString "chain_id" ≠ n) (L : GA)
    (v : ValueHOL 64) (h : SRP O L) : SRP O (L.update (n,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,let ⟨c,hc⟩ := h.2; ⟨c,by rw [lookup_update_ne' _ _ h2]; exact hc⟩⟩

/-- Entry `out` of a signing-hash callee `f(e1, .., var out_hash)` (last parameter `out`). -/
theorem entry_out_last {f : MlS} {ps : List (MlS × ShapeHOL)} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some (ps,bd,rs0)) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (O : BitVec 64) (ho : s.locals.lookup (ofString "out_hash") = some (.val (.word O)))
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "tx"),.var .local (ofString "out_hash")] = some values)
    (hps2 : ps = [(ofString "tx",.one),(ofString "out",.one)])
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    callee.lookup (ofString "out") = some (.val (.word O)) := by
  subst hps2
  obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  simp [EV,evalHOLExact,ho] at ev2; subst ev2
  have e := callee_eq inst lookup
  rw [e]; simp (config := {decide := true})

section sp
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat}

theorem rcallSH {f : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(ofString "tx",.one),(ofString "out",.one)],bd,rs0))
    (Lo Sc O : BitVec 64)
    (hb : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "out") = some (.val (.word O)) ∧ RG Lo Sc G) (fun _ _ _ => True)
      (fun _ _ G => RG Lo Sc G) bd) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => SRP O L ∧ RG Lo Sc G)
      (fun L _ G => SRP O L ∧ RG Lo Sc G) RR
      (.call (some (none,none)) f [.var .local (ofString "tx"),.var .local (ofString "out_hash")]) :=
  rcallK (GP := RG Lo Sc) (LP := SRP O) (Rv := fun _ => True) (fun L => L.lookup (ofString "out") = some (.val (.word O)))
    _ _ _ _ _ inst (aqgd_conseq hb (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs lp args lookup => entry_out_last inst s O lp.1 args rfl lookup)

/-- The `t == 0` branch of `signature_recovery_parameters` (legacy / EIP-155 hashes into `out_hash`). -/
theorem srpT0_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) {Q : GA → Mem → GA → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
    (hRR : ∀ v M G, RG Lo Sc G → RR v M G) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => SRP O L ∧ RG Lo Sc G) Q RR srpT0 := by
  unfold srpT0
  have ret : ∀ (e : ExpHOL 64) {Q' : GA → Mem → GA → Prop}, AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => SRP O L ∧ RG Lo Sc G) Q' RR (.return e) :=
    fun e Q' => aqgd_return _ (fun _ v _ _ _ ⟨_,rg⟩ _ _ => hRR v _ _ rg)
  have u := fun (n : MlS) (h1 : ofString "out_hash" ≠ n) (h2 : ofString "chain_id" ≠ n) => srp_upd (O := O) n h1 h2
  refine aqgd_seq (aqgd_iteT _ (aqgd_iteT _ (aqgd_seq (rcallSH originalRuntimeCode_signingHashPre155_lookup Lo Sc O
    (shPre_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO)) (ret _)) aqgd_skip) aqgd_skip) ?_
  refine decR0 (LP := SRP O) (GP := RG Lo Sc) (ofString "c") _ _ (u _ (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRP O) (ofString "x2") _ _ _ _ _ _ vmLookup_u256_add
    (memoryFrame_of_good vmLookup_u256_add (by decide) (by decide)) (by body_check Guest.guestFn_u256_add)
    (by body_check Guest.guestFn_u256_add) (u _ (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRP O) (ofString "v35") _ _ _ _ _ _ vmLookup_u256_add
    (memoryFrame_of_good vmLookup_u256_add (by decide) (by decide)) (by body_check Guest.guestFn_u256_add)
    (by body_check Guest.guestFn_u256_add) (u _ (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRP O) (ofString "v36") _ _ _ _ _ _ vmLookup_u256_add
    (memoryFrame_of_good vmLookup_u256_add (by decide) (by decide)) (by body_check Guest.guestFn_u256_add)
    (by body_check Guest.guestFn_u256_add) (u _ (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRP O) (ofString "eq35") _ _ _ _ _ _ vmLookup_u256_eq
    (memoryFrame_of_good vmLookup_u256_eq (by decide) (by decide)) (by body_check Guest.guestFn_u256_eq)
    (by body_check Guest.guestFn_u256_eq) (u _ (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRP O) (ofString "eq36") _ _ _ _ _ _ vmLookup_u256_eq
    (memoryFrame_of_good vmLookup_u256_eq (by decide) (by decide)) (by body_check Guest.guestFn_u256_eq)
    (by body_check Guest.guestFn_u256_eq) (u _ (by decide) (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_raise _ _) aqgd_skip) ?_
  refine aqgd_seq (rcallK (GP := RG Lo Sc) (LP := SRP O) (Rv := fun _ => True) (fun L =>
    L.lookup (ofString "out") = some (.val (.word O)) ∧ ∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c)))
    _ _ _ _ _ originalRuntimeCode_signingHash155_lookup
    (aqgd_conseq (sh155_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => ⟨trivial,h⟩))
    (fun s values callee rs ⟨ho,c,hc⟩ args lookup => by
      obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
      have := evalList_nil' s _ r3; subst this
      simp [EV,evalHOLExact,hc] at ev2; subst ev2
      simp [EV,evalHOLExact,ho] at ev3; subst ev3
      have e := callee_eq originalRuntimeCode_signingHash155_lookup lookup
      exact ⟨by rw [e]; simp (config := {decide := true}),c,by rw [e]; simp (config := {decide := true})⟩)) ?_
  exact ret _

#print axioms srpT0_wn

theorem srpTail_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => SRP O L ∧ RG Lo Sc G) Q
      (fun _ _ G => RG Lo Sc G) srpTail := by
  unfold srpTail
  have u := fun (n : MlS) (h1 : ofString "out_hash" ≠ n) (h2 : ofString "chain_id" ≠ n) => srp_upd (O := O) n h1 h2
  refine decR0 (LP := SRP O) (GP := RG Lo Sc) (ofString "t") _ _ (u _ (by decide) (by decide)) ?_
  refine decR0 (LP := SRP O) (GP := RG Lo Sc) (ofString "v") _ _ (u _ (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRP O) (ofString "fits") _ _ _ _ _ _ vmLookup_u256_fits_word
    (memoryFrame_of_good vmLookup_u256_fits_word (by decide) (by decide)) (by body_check Guest.guestFn_u256_fits_word)
    (by body_check Guest.guestFn_u256_fits_word) (u _ (by decide) (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (srpT0_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO (fun _ _ _ h => h)) aqgd_skip) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_raise _ _) aqgd_skip) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_raise _ _) aqgd_skip) ?_
  refine aqgd_seq (aqgd_iteT _ (rcallSH originalRuntimeCode_signingHash2930_lookup Lo Sc O (sh2930_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO))
    aqgd_skip) ?_
  refine aqgd_seq (aqgd_iteT _ (rcallSH originalRuntimeCode_signingHash1559_lookup Lo Sc O (sh1559_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO))
    aqgd_skip) ?_
  refine aqgd_seq (aqgd_iteT _ (rcallSH originalRuntimeCode_signingHash4844_lookup Lo Sc O (sh4844_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO))
    aqgd_skip) ?_
  refine aqgd_seq (aqgd_iteT _ (rcallSH originalRuntimeCode_signingHash7702_lookup Lo Sc O (sh7702_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO))
    aqgd_skip) ?_
  exact aqgd_return _ (fun _ _ _ _ _ ⟨_,rg⟩ _ _ => rg)

/-- The actual `signature_recovery_parameters(tx, chain_id, out_hash)`: only the signing hash writes, into
`[O, O + 32)` (and above the heap pointer, released); keeps `RG`. -/
theorem sigRecParams_wn (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd O : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hw : w.toNat < Lo.toNat)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => SRP O L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_signature_recovery_parameters) := by
  rw [srpTop_eq]; unfold srpTop
  have u := fun (n : MlS) (h1 : ofString "out_hash" ≠ n) (h2 : ofString "chain_id" ≠ n) => srp_upd (O := O) n h1 h2
  refine decR0 (LP := SRP O) (GP := RG Lo Sc) (ofString "r") _ _ (u _ (by decide) (by decide)) ?_
  refine decR0 (LP := SRP O) (GP := RG Lo Sc) (ofString "s") _ _ (u _ (by decide) (by decide)) ?_
  refine rdecMF (LP' := SRP O) (ofString "z") _ _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero) (u _ (by decide) (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_raise _ _) aqgd_skip) ?_
  refine rdecMF (LP' := SRP O) (ofString "lt") _ _ _ _ _ _ vmLookup_u256_lt
    (memoryFrame_of_good vmLookup_u256_lt (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt)
    (by body_check Guest.guestFn_u256_lt) (u _ (by decide) (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_raise _ _) aqgd_skip) ?_
  refine aqgd_seq (rcallMFS (LP := SRP O) (GP := RG Lo Sc) (ofString "z") _ _ _ _ _ vmLookup_u256_is_zero
    (memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide)) (by body_check Guest.guestFn_u256_is_zero)
    (by body_check Guest.guestFn_u256_is_zero) (u _ (by decide) (by decide))) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_raise _ _) aqgd_skip) ?_
  refine rdecMF (LP' := SRP O) (ofString "gt") _ _ _ _ _ _ vmLookup_u256_gt
    (memoryFrame_of_good vmLookup_u256_gt (by decide) (by decide)) (by body_check Guest.guestFn_u256_gt)
    (by body_check Guest.guestFn_u256_gt) (u _ (by decide) (by decide)) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_raise _ _) aqgd_skip) ?_
  exact srpTail_wn hF hDF hcap Lo Sc K Pd O hK0 hPd0 hw oK oP oO

#print axioms sigRecParams_wn
end sp
end InitECandidate.Runtime
