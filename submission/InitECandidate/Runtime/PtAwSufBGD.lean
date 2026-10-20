import InitECandidate.Runtime.PtAwSufAGDU
import InitECandidate.Runtime.PtAwCallXGD
/-!
The coinbase `create_ether(lds (be + 32), …)` call of drops 99-117 keeps the accounts-written side condition together
with the block-environment global (`hRce2_aw`).  The key is the coinbase pointer stored at `be + 32`: the `be` global is
carried in the R-slot (kept by `create_ether` under `BeKeep`), and the word at `be + 32` is framed by `PXR` (outside
the registry, not excluded) to its value `CB` in the base memory.  No alignment of `CB` is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section aw2
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA}
  {J C SKB Bo U Sc : BitVec 64} {n m : Nat} {c T : Fin n → BitVec 64} {Out Excl : BitVec 64 → Prop}
  {ko kd kA kB k16 : Fin n} {e : Fin m → Fin n} {ko' kd' kA' kB' : Fin m} {Ts Bs Taw H0 S Y Ix : BitVec 64}
  {M0 : Mem} {BA IA IS KB Ixb : BitVec 64}

theorem hRce2_aw (bk : BalKeep2) (bkb : BeKeep) (BE CB : BitVec 64) (hCBE : CB.toNat + 52 ≤ 33806089496)
    (hOutBE : Out (BE + 32#64)) (hExBE : ¬ Excl (BE + 32#64)) (hCB : M0 (BE + 32#64) = .word CB)
    (inj : ∀ i j, e i = e j → i = j) (hko : e ko' = ko) (hne : ∀ i, e i ≠ k16) (hkd : e kd' = kd)
    (hkA : e kA' = kA) (hkB : e kB' = kB) (hc16 : c k16 = Ts + 16#64)
    (ne : kd ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko)) (hawWs : KoWsL SP0 FM K Pd NB Taw)
    (jB : J.toNat + C.toNat * 32 ≤ P0.toNat) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LPSs S Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) ∧
        (AwR Out D B J C SKB Ts Taw M G ∧ G.lookup (ofString "be") = some (.val (.word BE))))
      (fun _ M G => AwR Out D B J C SKB Ts Taw M G ∧ G.lookup (ofString "be") = some (.val (.word BE))) (fun _ _ _ => False)
      (.call (some (none,none)) (ofString "create_ether") [(.load .one (.op .add [(.var .global (ofString "be")),(.const 32)])),(.rstruct [(.rfield 1 (.var .local (ofString "tf"))),(.rfield 2 (.var .local (ofString "tf"))),(.rfield 3 (.var .local (ofString "tf"))),(.rfield 4 (.var .local (ofString "tf")))])]) :=
  let X : GA → Prop := fun G => G.lookup (ofString "be") = some (.val (.word BE))
  aqgd_liftB bk (by simp [keepsG,balWatched,goodBal2_createEther])
    (aqgd_conseq (aqgd_keepGR X
      (aqgd_call_createEther_awX (LP := LPSs S Y Ix) X _ _ CB
        (fun s _ px xg v ev => by
          have xg' : s.globals.lookup (ofString "be") = some (.val (.word BE)) := xg
          obtain ⟨_,_,_,_,_,_,fr⟩ := px
          have hm : s.memory (BE + 32#64) = .word CB := (fr _ hOutBE hExBE).trans hCB
          by_cases dm : s.memaddrs (BE + 32#64)
          · simp [EV, evalHOLExact, evalListHOLExact, xg', valueIsWord, valueWord, wordOpHOL, wordOp,
              memLoadHOLExact, isWfShapeExactHOL, dm, hm] at ev
            exact ev.symm
          · simp [EV, evalHOLExact, evalListHOLExact, xg', valueIsWord, valueWord, wordOpHOL, wordOp,
              memLoadHOLExact, isWfShapeExactHOL, dm] at ev)
        hCBE inj hko hne hkd hkA hkB
        hc16 ne hAB hAo hBo hTs hBs hcA hcB hco hcd p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe
        hOutSafe hkoWs hawWs jB Dall)
      (fun s code xg => by
        show (evaluateHOLFiniteState s _).2.globals.lookup (ofString "be") = _
        rw [evaluate_keeps_be bkb _ (by decide) s code]; exact xg))
      (fun _ _ _ h => ⟨h, h.2.2⟩) (fun _ _ _ h => ⟨h.1, h.2⟩) (fun _ _ _ h => h))

/-- The sender `create_ether` call keeps the side condition and the block-environment global. -/
theorem hRce1_awB (bk : BalKeep2) (bkb : BeKeep) (BE : BitVec 64) (hSE : S.toNat + 52 ≤ 33806089496)
    (inj : ∀ i j, e i = e j → i = j) (hko : e ko' = ko) (hne : ∀ i, e i ≠ k16) (hkd : e kd' = kd)
    (hkA : e kA' = kA) (hkB : e kB' = kB) (hc16 : c k16 = Ts + 16#64)
    (ne : kd ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko)) (hawWs : KoWsL SP0 FM K Pd NB Taw)
    (jB : J.toNat + C.toNat * 32 ≤ P0.toNat) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LPSs S Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) ∧
        (AwR Out D B J C SKB Ts Taw M G ∧ G.lookup (ofString "be") = some (.val (.word BE))))
      (fun _ M G => AwR Out D B J C SKB Ts Taw M G ∧ G.lookup (ofString "be") = some (.val (.word BE))) (fun _ _ _ => False)
      (.call (some (none,none)) (ofString "create_ether") [(.var .local (ofString "sender")),(.rstruct [(.rfield 1 (.var .local (ofString "gra"))),(.rfield 2 (.var .local (ofString "gra"))),(.rfield 3 (.var .local (ofString "gra"))),(.rfield 4 (.var .local (ofString "gra")))])]) :=
  aqgd_conseq (aqgd_keepGR (fun G => G.lookup (ofString "be") = some (.val (.word BE)))
    (hRce1_awU bk hSE inj hko hne hkd hkA hkB hc16 ne hAB hAo hBo hTs hBs hcA hcB hco hcd p0 jfit hwJ hwP hOut hwS
      hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hawWs jB Dall)
    (fun s code xg => by
      show (evaluateHOLFiniteState s _).2.globals.lookup (ofString "be") = _
      rw [evaluate_keeps_be bkb _ (by decide) s code]; exact xg))
    (fun _ _ _ ⟨⟨lp, px⟩, aw, xg⟩ => ⟨⟨⟨lp, px⟩, aw⟩, xg⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

theorem hRbo_awB (BE : BitVec 64) (hBoC : ∀ k : BitVec 64, k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64 →
      (Out (Bo + k) ∧ ∀ i, Bo + k ≠ c i) ∧ Excl (Bo + k) ∧ w ≠ Bo + k) (hc16 : c k16 = Ts + 16#64) :
    ∀ (k y : BitVec 64) (M : Mem) (G : GA), (k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64) →
      (AwR Out D B J C SKB Ts Taw M G ∧ G.lookup (ofString "be") = some (.val (.word BE))) →
      (AwR Out D B J C SKB Ts Taw (fun x => if x = Bo + k then .word y else M x) G ∧
        G.lookup (ofString "be") = some (.val (.word BE))) :=
  fun k y M G hk h => ⟨hRbo_aw hBoC hc16 k y M G hk h.1, h.2⟩

#print axioms hRce2_aw
#print axioms hRce1_awB
#print axioms hRbo_awB
end aw2
end InitECandidate.Runtime
