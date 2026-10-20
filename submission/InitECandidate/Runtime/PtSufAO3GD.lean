import InitECandidate.Runtime.PtSufAO2GD
/-!
`ptSufAO2` with a memory side condition `R` threaded through the actual statements: kept by the memory-and-globals
keeping callees automatically, and by the two `create_ether` calls and the four block-output stores through explicit
preservation triples / closure facts (discharged for the concrete side condition by the content lemmas).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section wr
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR RR' : ValueHOL 64 → Mem → GA → Prop}

/-- A statement keeping `LP ∧ X` and a triple keeping a side condition `R` give a triple keeping `LP ∧ (X ∧ R)`. -/
theorem aqgd_withRX {LP : GA → Prop} {X R : Mem → GA → Prop} {p : ProgHOL 64}
    (h1 : AQGD D B A w Vn (fun L M G => LP L ∧ X M G) (fun L M G => LP L ∧ X M G) RR p)
    (h2 : AQGD D B A w Vn (fun L M G => (LP L ∧ X M G) ∧ R M G) (fun _ M G => R M G) RR' p) :
    AQGD D B A w Vn (fun L M G => LP L ∧ (X M G ∧ R M G)) (fun L M G => LP L ∧ (X M G ∧ R M G)) RR p :=
  aqgd_conseq (aqgd_and (aqgd_conseq h1 (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) h2)
    (fun _ _ _ ⟨lp,x,r⟩ => ⟨⟨lp,x⟩,r⟩) (fun _ _ _ ⟨⟨lp,x⟩,r⟩ => ⟨lp,x,r⟩) (fun _ _ _ h => h.1)

#print axioms aqgd_withRX
end wr

section wr2
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}
  {J C SKB Bo H0 U Sc : BitVec 64} {M0 : Mem}

/-- `aqgd_store_exclS` with a side condition closed under the store. -/
theorem aqgd_store_exclSR {LP : GA → Prop} {R : Mem → GA → Prop} {a : BitVec 64}
    (hRa : ∀ M G y, R M G → R (fun x => if x = a then .word y else M x) G) (d v : ExpHOL 64) (a' : BitVec 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc s.globals → DomD D B s →
      LP s.locals → PXR n c T Out ko D B Excl H0 M0 s.memory s.globals → EV s d = some (.val (.word a')))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals → EV s v = some x →
      ∃ y : BitVec 64, x = .val (.word y))
    (hwa : w ≠ a') (hOutA : Out a' ∧ ∀ i, a' ≠ c i) (hExA : Excl a') (ea : a' = a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ (PXR n c T Out ko D B Excl H0 M0 M G ∧ R M G))
      (fun L M G => LP L ∧ (PXR n c T Out ko D B Excl H0 M0 M G ∧ R M G)) RR (.store d v) := by
  subst ea
  refine aqgd_storeD _ _ (fun s H aw dom hG ⟨lp,px,r⟩ _ => ?_) (fun s x H _ _ _ ⟨lp,_⟩ _ ev => hv s x lp ev)
  unfold GIs at hG; subst hG
  obtain ⟨H1,Nj,hH,hle,reg,hn,fr⟩ := px
  refine ⟨a',hd s aw dom lp ⟨H1,Nj,hH,hle,reg,hn,fr⟩,hwa,fun y _ => ⟨lp,⟨H1,Nj,hH,hle,?_,hn,fun x ho hx => ?_⟩,
    hRa _ _ y r⟩⟩
  · exact regT_frame reg (fun x => x = a') (fun x hx => by subst hx; exact hOutA) (fun x hx => by simp [hx])
  · have : x ≠ a' := fun e => hx (e ▸ hExA)
    simp only [if_neg this]
    exact fr x ho hx

#print axioms aqgd_store_exclSR
end wr2

section sa3
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {Y : BitVec 64}
  {BA IA IS KB Ixb : BitVec 64}

/-- `ptSufAO2` with a memory side condition `R` threaded: kept by the memory-and-globals-keeping callees, by the two
`create_ether` calls (`hRce1`, `hRce2`) and by the four block-output counter stores (`hRbo`). -/
theorem ptSufAO3 {QM : Mem → GA → Prop} (bk : BalKeep2) (R : Mem → GA → Prop) (Ix : BitVec 64)
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
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x)
    -- the four block-output counters `bo + 0, 8, 16, 48` are outside words in the exception region
    (hBoC : ∀ k : BitVec 64, k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64 →
      (Out (Bo + k) ∧ ∀ i, Bo + k ≠ c i) ∧ Excl (Bo + k) ∧ w ≠ Bo + k)
    (hRce1 : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LPSo Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) ∧ R M G) (fun _ M G => R M G)
      (fun _ _ _ => False) (.call (some (none,none)) (ofString "create_ether") [(.var .local (ofString "sender")),(.rstruct [(.rfield 1 (.var .local (ofString "gra"))),(.rfield 2 (.var .local (ofString "gra"))),(.rfield 3 (.var .local (ofString "gra"))),(.rfield 4 (.var .local (ofString "gra")))])]))
    (hRce2 : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LPSo Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) ∧ R M G) (fun _ M G => R M G)
      (fun _ _ _ => False) (.call (some (none,none)) (ofString "create_ether") [(.load .one (.op .add [(.var .global (ofString "be")),(.const 32)])),(.rstruct [(.rfield 1 (.var .local (ofString "tf"))),(.rfield 2 (.var .local (ofString "tf"))),(.rfield 3 (.var .local (ofString "tf"))),(.rfield 4 (.var .local (ofString "tf")))])]))
    (hRbo : ∀ (k y : BitVec 64) (M : Mem) (G : GA), (k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64) → R M G →
      R (fun x => if x = Bo + k then .word y else M x) G)
    {cont : ProgHOL 64}
    (hcont : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LPSo Y Ix L ∧ (PXR n c T Out ko D B Excl H0 M0 M G ∧ R M G)) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LPSo Y Ix L ∧ (PXR n c T Out ko D B Excl H0 M0 M G ∧ R M G)) (fun _ M G => QM M G) RR
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
    (by simp [keepsG,balWatched,goodBal2_createEther]) <| aqgd_call_createEtherS (D := D) (B := B) (w := w) (LP := LPSo Y Ix) (RR := RR) (Bo := Bo) (U := U) (Sc := Sc)
    (Excl := Excl) (M0 := M0) e1 e2 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO
    hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE
  have stbo := fun (k : BitVec 64) (hk : k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64) (e : ExpHOL 64) =>
    aqgd_liftB (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ixb) bk (by simp [keepsG,balWatched]) <|
      aqgd_store_exclSR (R := R) (fun M G y => hRbo k y M G hk) (D := D) (B := B) (w := w) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB) (Bo := Bo) (LP := LPSo Y Ix) (RR := RR) (n := n) (c := c) (T := T) (Out := Out) (ko := ko) (Excl := Excl)
      (H0 := H0) (M0 := M0) (U := U) (Sc := Sc) (.op .add [.var .global (ofString "bo"),.const k])
      (.op .add [.load .one (.op .add [.var .global (ofString "bo"),.const k]),e]) (Bo + k)
      (fun s aw _ _ _ => by simp [EV,evalHOLExact,evalListHOLExact,aw.1.1.2,wordOpHOL,wordOp,valueIsWord,valueWord])
      (fun s x _ ev => ev_op_word s _ _ x ev) (hBoC k hk).2.2 (hBoC k hk).1 (hBoC k hk).2.1 rfl
  refine aqgd_dec_lpso _ _ _ (by decide) (by decide) ?_
  refine aqgd_decCall_lpso _ _ _ _ _ _ _ originalRuntimeCode_udivSmall5_lookup
    (memoryFrame_of_good originalRuntimeCode_udivSmall5_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_udiv_small5) (by body_check Guest.guestFn_udiv_small5) (by decide) (by decide) ?_
  refine aqgd_decCall_lpso _ _ _ _ _ _ _ originalRuntimeCode_min_lookup
    (memoryFrame_of_good originalRuntimeCode_min_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_min) (by body_check Guest.guestFn_min) (by decide) (by decide) ?_
  refine aqgd_dec_lpso _ _ _ (by decide) (by decide) ?_
  refine aqgd_decCall_lpso _ _ _ _ _ _ _ originalRuntimeCode_max_lookup
    (memoryFrame_of_good originalRuntimeCode_max_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_max) (by body_check Guest.guestFn_max) (by decide) (by decide) ?_
  refine aqgd_dec_lpso _ _ _ (by decide) (by decide) ?_
  refine aqgd_decCall_lpsSO _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup
    (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) (by decide) (by decide) ?_
  refine aqgd_decCall_lpsSO _ _ _ _ _ _ _ originalRuntimeCode_u256Sub_lookup
    (memoryFrame_of_good originalRuntimeCode_u256Sub_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_u256_sub) (by body_check Guest.guestFn_u256_sub) (by decide) (by decide) ?_
  refine aqgd_decCall_lpsSO _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup
    (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_withRX (ce _ _) hRce1) ?_
  refine aqgd_seq (aqgd_withRX (ce _ _) hRce2) ?_
  refine aqgd_dec_lpso _ _ _ (by decide) (by decide) ?_
  refine aqgd_dec_lpso _ _ _ (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_assignLocal _ _ (fun s v _ _ pre _ _ =>
    ⟨lpso_upd pre.1 _ v (by decide) (by decide),pre.2⟩)) aqgd_skip) ?_
  refine aqgd_decCall_lpso _ _ _ _ _ _ _ originalRuntimeCode_max_lookup
    (memoryFrame_of_good originalRuntimeCode_max_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_max) (by body_check Guest.guestFn_max) (by decide) (by decide) ?_
  refine aqgd_seq (stbo 0#64 (by decide) _) ?_
  refine aqgd_seq (stbo 8#64 (by decide) _) ?_
  refine aqgd_seq (stbo 48#64 (by decide) _) ?_
  refine aqgd_seq (stbo 16#64 (by decide) _) ?_
  exact hcont

#print axioms ptSufAO3
end sa3
end InitECandidate.Runtime
