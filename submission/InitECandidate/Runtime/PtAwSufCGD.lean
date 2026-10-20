import InitECandidate.Runtime.PtAwSufBGD
/-!
Drops 99-117 with the accounts-written side condition and the `be` global carried through (`ptSufAO4_awB`):
`ptSufAO4` instantiated with `R = AwR ∧ be`, its three R-slot obligations discharged by `hRce1_awB`, `hRce2_aw`
(coinbase key of any alignment) and `hRbo_awB`.  Under `BalKeep2` and `BeKeep`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section sa4b
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {Y : BitVec 64}
  {BA IA IS KB Ixb : BitVec 64}

theorem ptSufAO4_awB {QM : Mem → GA → Prop} (bk : BalKeep2) (bkb : BeKeep) (S Ix BE CB Taw : BitVec 64) {m : Nat}
    {e : Fin m → Fin n} {ko' kd' kA' kB' : Fin m}
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
    (hSfit : S.toNat + 52 ≤ 33806089496) (hCBE : CB.toNat + 52 ≤ 33806089496)
    (hOutBE : Out (BE + 32#64)) (hExBE : ¬ Excl (BE + 32#64)) (hCB : M0 (BE + 32#64) = .word CB)
    (inj : ∀ i j, e i = e j → i = j) (hko : e ko' = ko) (hne : ∀ i, e i ≠ k16) (hkd : e kd' = kd)
    (hkA : e kA' = kA) (hkB : e kB' = kB)
    (hawWs : KoWsL SP0 FM K Pd NB Taw) (jB : J.toNat + C.toNat * 32 ≤ P0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    {cont : ProgHOL 64}
    (hcont : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LPSs S Y Ix L ∧ (PXR n c T Out ko D B Excl H0 M0 M G ∧ (fun M G => AwR Out D B J C SKB Ts Taw M G ∧ G.lookup (ofString "be") = some (.val (.word BE))) M G)) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LPSs S Y Ix L ∧ (PXR n c T Out ko D B Excl H0 M0 M G ∧ (fun M G => AwR Out D B J C SKB Ts Taw M G ∧ G.lookup (ofString "be") = some (.val (.word BE))) M G)) (fun _ M G => QM M G) RR
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
  have hR1 := hRce1_awB (B := B) (Ix := Ix) (Y := Y) (H0 := H0) (M0 := M0) (Excl := Excl) (Bo := Bo) (U := U) (Sc := Sc)
    (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ixb := Ixb)
    bk bkb BE hSfit inj hko hne hkd hkA hkB hc16 ne hAB hAo hBo hTs hBs hcA hcB hco hcd p0 jfit hwJ hwP hOut hwS
    hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hawWs jB Dall
  have hR2 := hRce2_aw (B := B) (S := S) (Ix := Ix) (Y := Y) (H0 := H0) (Excl := Excl) (Bo := Bo) (U := U) (Sc := Sc)
    (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ixb := Ixb)
    bk bkb BE CB hCBE hOutBE hExBE hCB inj hko hne hkd hkA hkB hc16 ne hAB hAo hBo hTs hBs hcA hcB hco hcd p0 jfit
    hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hawWs jB Dall
  exact ptSufAO4 bk _ S Ix ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB
    hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE hBoC hR1 hR2 (hRbo_awB BE hBoC hc16) hcont

#print axioms ptSufAO4_awB
end sa4b
end InitECandidate.Runtime
