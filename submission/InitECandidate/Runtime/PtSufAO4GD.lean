import InitECandidate.Runtime.PtSufAO3GDL
/-!
`ptSufAO3L` with the `sender` local pinned to its value `S` (`LPSs`): no statement of drops 99-117 assigns `sender`, so
the pin survives, and the `create_ether(sender, …)` call's key is the known pointer `S`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- `LPSo` with the `sender` local pinned. -/
def LPSs (S Y Ix : BitVec 64) (L : GA) : Prop :=
  LPSo Y Ix L ∧ L.lookup (ofString "sender") = some (.val (.word S))

theorem lpss_upd {S Y Ix : BitVec 64} {L : GA} (h : LPSs S Y Ix L) (name : MlS) (v : ValueHOL 64)
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out") :
    LPSs S Y Ix (L.update (name,v)) :=
  ⟨lpso_upd h.1 name v ne ne',by rw [lookup_update_ne' _ _ (Ne.symm ne'.1)]; exact h.2⟩

theorem lpss_res {S Y Ix : BitVec 64} {L : GA} (h : LPSs S Y Ix L) (name : MlS) (o : Option (ValueHOL 64))
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out") :
    LPSs S Y Ix (L.resVarEq (name,o)) :=
  ⟨lpso_res h.1 name o ne ne',by rw [resVarEq_lookup_ne' _ _ _ _ (Ne.symm ne'.1)]; exact h.2⟩

section px
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {X : Mem → GA → Prop} {QM : Mem → GA → Prop} {Ix Y S : BitVec 64}

theorem aqgd_dec_lpss (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out")
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPSs S Y Ix L ∧ X M G) (fun _ M G => QM M G) RR body) :
    AQGD D B A w (fun _ => False) (fun L M G => LPSs S Y Ix L ∧ X M G) (fun _ M G => QM M G) RR
      (.dec name shape init body) :=
  aqgd_dec _ _ _ (fun h => h.elim) (fun _ v _ _ _ pre _ _ _ => ⟨lpss_upd pre.1 _ v ne ne',pre.2⟩) hb
    (fun _ _ _ _ _ _ _ h => h)

theorem aqgd_decCall_lpss (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out")
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPSs S Y Ix L ∧ X M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B A w (fun _ => False) (fun L M G => LPSs S Y Ix L ∧ X M G) (fun _ M G => QM M G) RR
      (.decCall name shape function arguments cont) :=
  aqgd_decCall_mfF _ _ _ _ _ _ _ installed mf nb nc (fun _ _ _ v pre => ⟨lpss_upd pre.1 _ v ne ne',pre.2⟩) hb
    (fun _ _ _ _ _ _ _ h => h)

/-- A declared call to a memory-and-globals-keeping function with any parameter shapes, keeping `LPSs S Y`. -/
theorem aqgd_decCall_lpsSS (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out")
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPSs S Y Ix L ∧ X M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B A w (fun _ => False) (fun L M G => LPSs S Y Ix L ∧ X M G) (fun _ M G => QM M G) RR
      (.decCall name shape function arguments cont) :=
  aqgd_decCallSpecS (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => LPSs S Y Ix L ∧ X M G) (Qc := fun _ M G => QM M G) _ _ _ _ _ _ _ installed
    (fun _ _ _ _ _ h => h.elim) (fun _ M0' G0' _ => aqgd_of_mf mf nb nc M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim)
    (fun L M G v M' G' pre ⟨e1,e2⟩ _ => by rw [e1,e2]; exact ⟨lpss_upd pre.1 _ v ne ne',pre.2⟩) hb
    (fun _ _ _ _ _ _ _ h => h)

#print axioms aqgd_decCall_lpsSS
end px

section sa4
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {Y : BitVec 64}
  {BA IA IS KB Ixb : BitVec 64}

/-- `ptSufAO2L` with a memory side condition `R` threaded: kept by the memory-and-globals-keeping callees, by the two
`create_ether` calls (`hRce1`, `hRce2`) and by the four block-output counter stores (`hRbo`). -/
theorem ptSufAO4 {QM : Mem → GA → Prop} (bk : BalKeep2) (R : Mem → GA → Prop) (S Ix : BitVec 64)
    (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x)
    -- the four block-output counters `bo + 0, 8, 16, 48` are outside words in the exception region
    (hBoC : ∀ k : BitVec 64, k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64 →
      (Out (Bo + k) ∧ ∀ i, Bo + k ≠ c i) ∧ Excl (Bo + k) ∧ w ≠ Bo + k)
    (hRce1 : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LPSs S Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) ∧ R M G) (fun _ M G => R M G)
      (fun _ _ _ => False) (.call (some (none,none)) (ofString "create_ether") [(.var .local (ofString "sender")),(.rstruct [(.rfield 1 (.var .local (ofString "gra"))),(.rfield 2 (.var .local (ofString "gra"))),(.rfield 3 (.var .local (ofString "gra"))),(.rfield 4 (.var .local (ofString "gra")))])]))
    (hRce2 : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LPSs S Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) ∧ R M G) (fun _ M G => R M G)
      (fun _ _ _ => False) (.call (some (none,none)) (ofString "create_ether") [(.load .one (.op .add [(.var .global (ofString "be")),(.const 32)])),(.rstruct [(.rfield 1 (.var .local (ofString "tf"))),(.rfield 2 (.var .local (ofString "tf"))),(.rfield 3 (.var .local (ofString "tf"))),(.rfield 4 (.var .local (ofString "tf")))])]))
    (hRbo : ∀ (k y : BitVec 64) (M : Mem) (G : GA), (k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64) → R M G →
      R (fun x => if x = Bo + k then .word y else M x) G)
    {cont : ProgHOL 64}
    (hcont : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LPSs S Y Ix L ∧ (PXR n c T Out ko D B Excl H0 M0 M G ∧ R M G)) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LPSs S Y Ix L ∧ (PXR n c T Out ko D B Excl H0 M0 M G ∧ R M G)) (fun _ M G => QM M G) RR
      (.dec (ofString "used_before_refund") .one (.op .sub [(.op .sub [(.var .local (ofString "gas")),(.load .one (.op .add [(.var .local (ofString "out")),(.const 0)]))]),(.load .one (.op .add [(.var .local (ofString "out")),(.const 56)]))])
        (.decCall (ofString "ubr5") .one (ofString "udiv_small5") [(.var .local (ofString "used_before_refund"))]
        (.decCall (ofString "refund") .one (ofString "min") [(.var .local (ofString "ubr5")),(.load .one (.op .add [(.var .local (ofString "out")),(.const 8)]))]
        (.dec (ofString "used_after_refund") .one (.op .sub [(.var .local (ofString "used_before_refund")),(.var .local (ofString "refund"))])
        (.decCall (ofString "tx_gas_used") .one (ofString "max") [(.var .local (ofString "used_after_refund")),(.rfield 2 (.var .local (ofString "intrinsic")))]
        (.dec (ofString "tx_gas_left") .one (.op .sub [(.var .local (ofString "gas")),(.var .local (ofString "tx_gas_used"))])
        (.decCall (ofString "gra") (.comb [.one,.one,.one,.one,.one]) (ofString "fee_mul") [(.var .local (ofString "tx_gas_left")),(.var .local (ofString "price"))]
        (.decCall (ofString "priority_fee") (.comb [.one,.one,.one,.one]) (ofString "u256_sub") [(.var .local (ofString "price")),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .global (ofString "be")),(.const 48)]))]
        (.decCall (ofString "tf") (.comb [.one,.one,.one,.one,.one]) (ofString "fee_mul") [(.var .local (ofString "tx_gas_used")),(.var .local (ofString "priority_fee"))]
        (.seq (.call (some (none,none)) (ofString "create_ether") [(.var .local (ofString "sender")),(.rstruct [(.rfield 1 (.var .local (ofString "gra"))),(.rfield 2 (.var .local (ofString "gra"))),(.rfield 3 (.var .local (ofString "gra"))),(.rfield 4 (.var .local (ofString "gra")))])])
        (.seq (.call (some (none,none)) (ofString "create_ether") [(.load .one (.op .add [(.var .global (ofString "be")),(.const 32)])),(.rstruct [(.rfield 1 (.var .local (ofString "tf"))),(.rfield 2 (.var .local (ofString "tf"))),(.rfield 3 (.var .local (ofString "tf"))),(.rfield 4 (.var .local (ofString "tf")))])])
        (.dec (ofString "tx_state_gas") .one (.op .add [(.rfield 1 (.var .local (ofString "intrinsic"))),(.load .one (.op .add [(.var .local (ofString "out")),(.const 72)]))])
        (.dec (ofString "tx_state_gas_nat") .one (.var .local (ofString "tx_state_gas"))
        (.seq (.ite (.cmp .less (.var .local (ofString "tx_state_gas")) (.const 0)) (.assign .local (ofString "tx_state_gas_nat") (.const 0)) .skip)
        (.decCall (ofString "tx_regular_gas") .one (ofString "max") [(.op .sub [(.var .local (ofString "used_before_refund")),(.var .local (ofString "tx_state_gas_nat"))]),(.rfield 2 (.var .local (ofString "intrinsic")))]
        (.seq (.store (.op .add [(.var .global (ofString "bo")),(.const 0)]) (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),(.const 0)])),(.var .local (ofString "tx_regular_gas"))]))
        (.seq (.store (.op .add [(.var .global (ofString "bo")),(.const 8)]) (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),(.const 8)])),(.var .local (ofString "tx_state_gas_nat"))]))
        (.seq (.store (.op .add [(.var .global (ofString "bo")),(.const 48)]) (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),(.const 48)])),(.var .local (ofString "tx_blob_gas_used"))]))
        (.seq (.store (.op .add [(.var .global (ofString "bo")),(.const 16)]) (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),(.const 16)])),(.var .local (ofString "tx_gas_used"))]))
        cont))))))))))))))))))) := by
  have ce := fun (e1 e2 : ExpHOL 64) => aqgd_liftB (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ixb) bk
    (by simp [keepsG,balWatched,goodBal2_createEther]) <| aqgd_call_createEtherSL (D := D) (B := B) (w := w) (LP := LPSs S Y Ix) (RR := RR) (Bo := Bo) (U := U) (Sc := Sc)
    (Excl := Excl) (M0 := M0) e1 e2 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO
    hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE
  have stbo := fun (k : BitVec 64) (hk : k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64) (e : ExpHOL 64) =>
    aqgd_liftB (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ixb) bk (by simp [keepsG,balWatched]) <|
      aqgd_store_exclSR (R := R) (fun M G y => hRbo k y M G hk) (D := D) (B := B) (w := w) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB) (Bo := Bo) (LP := LPSs S Y Ix) (RR := RR) (n := n) (c := c) (T := T) (Out := Out) (ko := ko) (Excl := Excl)
      (H0 := H0) (M0 := M0) (U := U) (Sc := Sc) (.op .add [.var .global (ofString "bo"),.const k])
      (.op .add [.load .one (.op .add [.var .global (ofString "bo"),.const k]),e]) (Bo + k)
      (fun s aw _ _ _ => by simp [EV,evalHOLExact,evalListHOLExact,aw.1.1.2,wordOpHOL,wordOp,valueIsWord,valueWord])
      (fun s x _ ev => ev_op_word s _ _ x ev) (hBoC k hk).2.2 (hBoC k hk).1 (hBoC k hk).2.1 rfl
  refine aqgd_dec_lpss _ _ _ (by decide) (by decide) ?_
  refine aqgd_decCall_lpss _ _ _ _ _ _ _ originalRuntimeCode_udivSmall5_lookup
    (memoryFrame_of_good originalRuntimeCode_udivSmall5_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_udiv_small5) (by body_check Guest.guestFn_udiv_small5) (by decide) (by decide) ?_
  refine aqgd_decCall_lpss _ _ _ _ _ _ _ originalRuntimeCode_min_lookup
    (memoryFrame_of_good originalRuntimeCode_min_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_min) (by body_check Guest.guestFn_min) (by decide) (by decide) ?_
  refine aqgd_dec_lpss _ _ _ (by decide) (by decide) ?_
  refine aqgd_decCall_lpss _ _ _ _ _ _ _ originalRuntimeCode_max_lookup
    (memoryFrame_of_good originalRuntimeCode_max_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_max) (by body_check Guest.guestFn_max) (by decide) (by decide) ?_
  refine aqgd_dec_lpss _ _ _ (by decide) (by decide) ?_
  refine aqgd_decCall_lpsSS _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup
    (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) (by decide) (by decide) ?_
  refine aqgd_decCall_lpsSS _ _ _ _ _ _ _ originalRuntimeCode_u256Sub_lookup
    (memoryFrame_of_good originalRuntimeCode_u256Sub_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_u256_sub) (by body_check Guest.guestFn_u256_sub) (by decide) (by decide) ?_
  refine aqgd_decCall_lpsSS _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup
    (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_withRX (ce _ _) hRce1) ?_
  refine aqgd_seq (aqgd_withRX (ce _ _) hRce2) ?_
  refine aqgd_dec_lpss _ _ _ (by decide) (by decide) ?_
  refine aqgd_dec_lpss _ _ _ (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_assignLocal _ _ (fun s v _ _ pre _ _ =>
    ⟨lpss_upd pre.1 _ v (by decide) (by decide),pre.2⟩)) aqgd_skip) ?_
  refine aqgd_decCall_lpss _ _ _ _ _ _ _ originalRuntimeCode_max_lookup
    (memoryFrame_of_good originalRuntimeCode_max_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_max) (by body_check Guest.guestFn_max) (by decide) (by decide) ?_
  refine aqgd_seq (stbo 0#64 (by decide) _) ?_
  refine aqgd_seq (stbo 8#64 (by decide) _) ?_
  refine aqgd_seq (stbo 48#64 (by decide) _) ?_
  refine aqgd_seq (stbo 16#64 (by decide) _) ?_
  exact hcont

#print axioms ptSufAO4
end sa4
end InitECandidate.Runtime
